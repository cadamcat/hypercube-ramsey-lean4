import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal_repeats

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Independent primitive records factor tests with disjoint consultations. -/
theorem pi_local_prod {A R : Type*} [DecidableEq A] [Fintype R] [DecidableEq R]
    {Ω : R → Type*} [∀ r, Fintype (Ω r)]
    (P : ∀ r, FinLaw (Ω r)) (S : Finset A) (scope : A → Finset R)
    (f : A → (∀ r, Ω r) → ℝ)
    (hdep : ∀ a ∈ S, ∀ x y, (∀ r ∈ scope a, x r = y r) → f a x = f a y)
    (hdis : (S : Set A).Pairwise (fun a b => Disjoint (scope a) (scope b))) :
    (FinLaw.pi P).E (fun x => ∏ a ∈ S, f a x) =
      ∏ a ∈ S, (FinLaw.pi P).E (f a) := by
  revert hdep hdis
  induction S using Finset.induction_on with
  | empty => intro hdep hdis; simp [expect_const]
  | @insert a S ha ih =>
    intro hdep hdis
    simp only [Finset.prod_insert ha]
    have hdepS : ∀ x y, (∀ r ∈ S.biUnion scope, x r = y r) →
        (∏ b ∈ S, f b x) = ∏ b ∈ S, f b y := by
      intro x y hxy
      apply Finset.prod_congr rfl
      intro b hb
      apply hdep b (Finset.mem_insert_of_mem hb) x y
      intro r hr
      exact hxy r (Finset.mem_biUnion.mpr ⟨b, hb, hr⟩)
    have hd : Disjoint (scope a) (S.biUnion scope) := by
      apply Finset.disjoint_left.mpr
      intro r hra hrS
      obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.mp hrS
      exact Finset.disjoint_left.mp
        (hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hb)
          (by intro he; subst b; exact ha hb)) hra hrb
    have hmul : (FinLaw.pi P).E (fun x => f a x * ∏ b ∈ S, f b x) =
        (FinLaw.pi P).E (f a) * (FinLaw.pi P).E (fun x => ∏ b ∈ S, f b x) := by
      have h := FinProb.pi_expect_mul_of_disjoint (fun r => S16.finLawToFramework (P r))
        (f a) (fun x => ∏ b ∈ S, f b x) (scope a) (S.biUnion scope)
        (hdep a (Finset.mem_insert_self _ _)) hdepS hd
      exact h
    rw [hmul, ih (fun b hb => hdep b (Finset.mem_insert_of_mem hb))
      (hdis.mono (Finset.subset_insert _ _))]

open S16.Lane_q_s16_comp2

theorem map_equiv_weight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (e : A ≃ B) (b : B) : (FinLaw.map P e).w b = P.w (e.symm b) := by
  classical
  unfold FinLaw.map
  change (∑ a : A, if e a = b then P.w a else 0) = P.w (e.symm b)
  rw [Finset.sum_eq_single (e.symm b)]
  · simp
  · intro a _ ha
    have he : e a ≠ b := by
      intro he
      apply ha
      simpa only [Equiv.symm_apply_apply] using congrArg e.symm he
    simp [he]
  · simp

theorem map_product {R : Type*} [Fintype R] [DecidableEq R]
    {Ω Ξ : R → Type*} [∀ r, Fintype (Ω r)] [∀ r, Fintype (Ξ r)]
    [∀ r, DecidableEq (Ξ r)] (P : ∀ r, FinLaw (Ω r)) (f : ∀ r, Ω r → Ξ r) :
    FinLaw.map (FinLaw.pi P) (fun x r => f r (x r)) =
      FinLaw.pi (fun r => FinLaw.map (P r) (f r)) := by
  classical
  apply finLaw_ext
  intro y
  have hpoint (x : ∀ r, Ω r) :
      (if (fun r => f r (x r)) = y then ∏ r, (P r).w (x r) else 0) =
        ∏ r, if f r (x r) = y r then (P r).w (x r) else 0 := by
    by_cases he : (fun r => f r (x r)) = y
    · rw [if_pos he]
      apply Finset.prod_congr rfl
      intro r _
      rw [if_pos (congrFun he r)]
    · rw [if_neg he]
      have hm : ∃ r, f r (x r) ≠ y r := by
        by_contra hn
        apply he
        funext r
        exact not_not.mp (fun h => hn ⟨r, h⟩)
      obtain ⟨r, hr⟩ := hm
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])
  change (∑ x : ∀ r, Ω r, if (fun r => f r (x r)) = y then ∏ r, (P r).w (x r) else 0) =
    ∏ r, ∑ x, if f r x = y r then (P r).w x else 0
  simp_rw [hpoint]
  exact (Fintype.prod_sum (fun r x => if f r x = y r then (P r).w x else 0)).symm

theorem map_product_expect {R : Type*} [Fintype R] [DecidableEq R]
    {Ω Ξ : R → Type*} [∀ r, Fintype (Ω r)] [∀ r, Fintype (Ξ r)]
    [∀ r, DecidableEq (Ξ r)] (P : ∀ r, FinLaw (Ω r)) (f : ∀ r, Ω r → Ξ r)
    (g : (∀ r, Ξ r) → ℝ) :
    (FinLaw.pi (fun r => FinLaw.map (P r) (f r))).E g =
      (FinLaw.pi P).E (fun x => g (fun r => f r (x r))) := by
  rw [← map_product P f, S16.Lane_q_s16_comp2.map_expect]

theorem cond_test_bound {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Finset Ω)
    (hA : 0 < ∑ x ∈ A, P.w x) (δ : ℝ) (hδ : δ < 1)
    (hMass : 1 - δ ≤ ∑ x ∈ A, P.w x) (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (FinLaw.cond P A hA).E f ≤ (1 - δ)⁻¹ * P.E f := by
  classical
  let m := ∑ x ∈ A, P.w x
  have hm : 0 < m := hA
  have hδpos : 0 < 1 - δ := by linarith
  have hnum : P.E (fun x => if x ∈ A then f x else 0) ≤ P.E f := by
    apply expect_le
    intro x
    by_cases hx : x ∈ A <;> simp [hx, hf x]
  calc
    (FinLaw.cond P A hA).E f = P.E (fun x => if x ∈ A then f x else 0) / m := by
      unfold FinLaw.E
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      change ((if x ∈ A then P.w x else 0) / m) * f x =
        (P.w x * (if x ∈ A then f x else 0)) / m
      by_cases hx : x ∈ A <;> simp [hx] <;> ring
    _ ≤ P.E f / m := div_le_div_of_nonneg_right hnum hm.le
    _ ≤ P.E f / (1 - δ) :=
      div_le_div_of_nonneg_left (expect_nonneg P f hf) hδpos hMass
    _ = _ := by ring

/-- Remove conditioning only on queried slices; unused slices cost one. -/
theorem conditioned_prod_bound {R : Type*} [Fintype R] [DecidableEq R]
    {Ω : R → Type*} [∀ r, Fintype (Ω r)] (P : ∀ r, FinLaw (Ω r))
    (A : ∀ r, Finset (Ω r)) (hA : ∀ r, 0 < ∑ x ∈ A r, (P r).w x)
    (δ : ℝ) (hδ : δ < 1) (hMass : ∀ r, 1 - δ ≤ ∑ x ∈ A r, (P r).w x)
    (S : Finset R) (f : ∀ r, Ω r → ℝ) (hf : ∀ r x, 0 ≤ f r x) :
    (FinLaw.pi fun r => FinLaw.cond (P r) (A r) (hA r)).E
      (fun x => ∏ r ∈ S, f r (x r)) ≤
      (1 - δ)⁻¹ ^ S.card * (FinLaw.pi P).E (fun x => ∏ r ∈ S, f r (x r)) := by
  rw [pi_consulted]
  calc
    (∏ r ∈ S, (FinLaw.cond (P r) (A r) (hA r)).E (f r)) ≤
        ∏ r ∈ S, (1 - δ)⁻¹ * (P r).E (f r) := by
      apply Finset.prod_le_prod₀
      · intro r _
        exact expect_nonneg _ _ (hf r)
      · intro r _
        exact cond_test_bound (P r) (A r) (hA r) δ hδ (hMass r) (f r) (hf r)
    _ = (1 - δ)⁻¹ ^ S.card * ∏ r ∈ S, (P r).E (f r) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = _ := by rw [pi_consulted]

noncomputable def solverQueryMoment {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r)
    (f : Fin (T.S.N k) → ℝ) : ℝ :=
  ∑ b : Bin 𝒯 i, S.q g W b * ∑ y, S.U g W b y * f y

theorem solver_query_local {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (f : Fin (T.S.N k) → ℝ)
    (W W' : ∀ r, S.Val r)
    (hW : ∀ r ∈ recordNear S.loc (groupCenter g).1, W r = W' r) :
    solverQueryMoment S g W f = solverQueryMoment S g W' f := by
  have hnear : ∀ r, (hammingDist (S.loc r) (groupCenter g).1 : ℝ) ≤
      10 * κ.ρ * (𝒯.P i).h → W r = W' r := by
    intro r hr
    exact hW r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩)
  unfold solverQueryMoment
  rw [S.q_local g W W' hnear]
  apply Finset.sum_congr rfl
  intro b _
  rw [S.U_local g W W' b hnear]

/-- Each unrestricted local test has exactly the prescribed raw mean. -/
theorem solver_query_mean {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (p : mesh.Param) (g : Group 𝒯 i)
    (f : Fin (T.S.N k) → ℝ) :
    (S.recLaw p).E (fun W => solverQueryMoment S g W f) =
      ∑ y, S.oddMean p g y * f y := by
  classical
  unfold solverQueryMoment FinLaw.E
  calc
    _ = ∑ W, ∑ y, (∑ b : Bin 𝒯 i, (S.recLaw p).w W * (S.q g W b * S.U g W b y)) * f y := by
      apply Finset.sum_congr rfl
      intro W _
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ y, (∑ W, ∑ b : Bin 𝒯 i, (S.recLaw p).w W * (S.q g W b * S.U g W b y)) * f y := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      unfold SliceSolver.oddMean SliceSolver.oddMarginal FinLaw.E
      simp_rw [Finset.mul_sum]

theorem solver_query_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} {mesh : Mesh 𝒯}
    (S : SliceSolver κ 𝒯 i mesh) (g : Group 𝒯 i) (W : ∀ r, S.Val r)
    (f : Fin (T.S.N k) → ℝ) (hf : ∀ y, 0 ≤ f y) :
    0 ≤ solverQueryMoment S g W f := by
  unfold solverQueryMoment
  apply Finset.sum_nonneg
  intro b _
  apply mul_nonneg (S.q_nonneg g W b)
  exact Finset.sum_nonneg (fun y _ => mul_nonneg (S.U_nonneg g W b y) (hf y))

theorem profiled_solver_query_mean {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (hc : PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) (S : SliceSolver κ PT.tiling i PT.mesh)
    (hS : PT.solver i = some S) (g : Group PT.tiling i) (f : Fin (T.S.N k) → ℝ) :
    (S.recLaw PT.parameter).E (fun W => solverQueryMoment S g W f) =
      ∑ y, (PT.πraw i).w y * f y := by
  rw [solver_query_mean]
  apply Finset.sum_congr rfl
  intro y _
  rw [hPT.raw_profile hc i S hS g y]

/-- Once slice conditioning is removed, disjoint local consultations have
the exact product of their raw-profile test means. -/
theorem solver_slice_factorization {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (hc : PT.tiling.mode.isCluster)
    (i : Fin PT.tiling.m) (S : SliceSolver κ PT.tiling i PT.mesh)
    (hS : PT.solver i = some S) {A : Type*} [Fintype A] [DecidableEq A]
    (g : A → Group PT.tiling i) (f : A → Fin (T.S.N k) → ℝ)
    (hdis : ((Finset.univ : Finset A) : Set A).Pairwise (fun a b =>
      Disjoint (recordNear S.loc (g a).1) (recordNear S.loc (g b).1))) :
    (S.recLaw PT.parameter).E (fun W => ∏ a, solverQueryMoment S (g a) W (f a)) =
      ∏ a, ∑ y, (PT.πraw i).w y * f a y := by
  classical
  let P : ∀ r, FinLaw (S.Val r) := fun r =>
    ⟨S.lawRec PT.parameter r, S.lawRec_nonneg PT.parameter r, S.lawRec_sum PT.parameter r⟩
  have hLaw : S.recLaw PT.parameter = FinLaw.pi P := rfl
  calc
    _ = ∏ a, (S.recLaw PT.parameter).E (fun W => solverQueryMoment S (g a) W (f a)) := by
      rw [hLaw]
      apply pi_local_prod P Finset.univ (fun a => recordNear S.loc (g a).1)
      · intro a _ W W' hW
        exact solver_query_local S (g a) (f a) W W' hW
      · exact hdis
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a _
      exact profiled_solver_query_mean hPT hc i S hS (g a) (f a)

noncomputable def rawQueryMoment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : S16.Lane_sol_fix2_s16.CellRawData G)
    (C : G.Cell) (r : S16.OddCellRole G C) (W : R.Hist C) (f : Fin (T.S.N k) → ℝ) : ℝ :=
  ∑ b, (R.qraw C W (R.groupOf C r)).w b *
    ∑ y, (R.U C W (R.groupOf C r) b).w y * f y

/-- The unconditioned physical slice records give exactly the product of
raw-profile means for separated queries in one cell. -/
theorem source_cluster_raw_factorization {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (hPT : PT.Valid)
    (R : S16.Lane_sol_fix2_s16.CellRawData G) (hR : R.SourceValid)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) {A : Type*} [Fintype A] [DecidableEq A]
    (r : A → S16.OddCellRole G C) (f : A → Fin (T.S.N k) → ℝ)
    (hMargin : 2 < 20 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ)) :
    (R.rawHistory C).E (fun W => ∏ a, rawQueryMoment R C (r a) W (f a)) =
      ∏ a, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y := by
  classical
  rcases hR with ⟨hm, hUniform, hSource⟩ | ⟨hd, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let loc := fun a => (R.cellWords C).symm ⟨(r a).1, (r a).2.1⟩
    let c := fun a => (loc a).1
    let ψ := fun a W => solverQueryMoment S (S.groupOf (loc a).2) W (f a)
    have epos (a : A) : (R.cellWords C (loc a)).1 = (r a).1 :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply _)
    have hOdd (a : A) : ¬ IsEvenRole (R.cellWords C (loc a)).1 := by
      rw [epos]; exact (r a).2.2
    have hGrp (a : A) : R.groupOf C (r a) = groups ((loc a).1, S.groupOf (loc a).2) := by
      have h := hGroup (loc a).1 (loc a).2 (hOdd a)
      have he : (⟨(R.cellWords C (loc a)).1, (R.cellWords C (loc a)).2, hOdd a⟩ : S16.OddCellRole G C) = r a :=
        Subtype.ext (epos a)
      rw [he] at h
      exact h
    have hMoment (a : A) (W : R.Hist C) :
        rawQueryMoment R C (r a) W (f a) = ψ a (records (c a) (W (c a))) := by
      unfold rawQueryMoment
      rw [hGrp]
      apply Finset.sum_congr rfl
      intro b _
      rw [hQ]
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      rw [hU]
    have hTransport : (R.rawHistory C).E
        (fun W => ∏ a, ψ a (records (c a) (W (c a)))) =
        (FinLaw.pi fun _ : R.Slice C => S.recLaw PT.parameter).E
          (fun W => ∏ a, ψ a (W (c a))) := by
      unfold S16.Lane_sol_fix2_s16.CellRawData.rawHistory
      rw [show R.sliceLaw C = (fun s => FinLaw.map (S.recLaw PT.parameter) (records s).symm)
        from funext hLaw]
      rw [map_product_expect]
      simp only [Equiv.apply_symm_apply]
    let test (s : R.Slice C) (W : ∀ j, S.Val j) :=
      ∏ a : {a : A // c a = s}, ψ a.1 W
    have hpoint (W : R.Slice C → (∀ j, S.Val j)) :
        (∏ a, ψ a (W (c a))) = ∏ s, test s (W s) := by
      rw [← Fintype.prod_fiberwise c (fun a => ψ a (W (c a)))]
      apply Finset.prod_congr rfl
      intro s _
      apply Finset.prod_congr rfl
      intro a _
      rw [a.2]
    calc
      _ = (R.rawHistory C).E (fun W => ∏ a, ψ a (records (c a) (W (c a)))) := by
        apply congrArg
        funext W
        exact Finset.prod_congr rfl (fun a _ => hMoment a W)
      _ = (FinLaw.pi fun _ : R.Slice C => S.recLaw PT.parameter).E
          (fun W => ∏ a, ψ a (W (c a))) := hTransport
      _ = ∏ s : R.Slice C, (S.recLaw PT.parameter).E (test s) := by
        simp_rw [hpoint]
        exact S16.Lane_q_s16_comp2.pi_expect_prod _ test
      _ = _ := by
        rw [← Fintype.prod_fiberwise c (fun a => ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y)]
        apply Finset.prod_congr rfl
        intro s _
        apply solver_slice_factorization hPT hc (G.cellPatch C) S hS
        intro a _ b _ hab
        apply query_consultations R hc C S r hMargin hSep a.1 b.1
          (fun he => hab (Subtype.ext he))
        exact a.2.trans b.2.symm
  · exact (hd hc).elim

theorem map_pi_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (d : ∀ i, Ω i) (i : I) [DecidableEq (Ω i)] :
    FinLaw.map (FinLaw.pi P) (fun x => x i) = P i := by
  classical
  apply finLaw_ext
  intro y
  let test := fun x : Ω i => if x = y then (1 : ℝ) else 0
  have h := (S16.Lane_q_s16_comp2.map_expect (FinLaw.pi P) (fun x => x i) test).trans
    (pi_coordinate P d i test)
  have he (Q : FinLaw (Ω i)) : Q.E test = Q.w y := by
    unfold FinLaw.E
    rw [Finset.sum_eq_single y]
    · simp [test]
    · intro x _ hx; simp [test, hx]
    · simp
  rw [he, he] at h
  exact h

/-- Identify the actual iid cell marginal with the uniform iid-slot law
used in the Section 16 containment calculation. -/
theorem cell_pool_law_iid {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT) (C : D.geom.Cell)
    (hBins : (Finset.univ : Finset (Bin PT.tiling (D.geom.cellPatch C))).Nonempty) :
    D.cellPoolLaw C = S16.iidCellPoolLaw (G := D.geom) C hBins := by
  classical
  let d := D.encoding.pools_nonempty.choose
  let P := fun C => FinLaw.uniform Finset.univ
    (show (Finset.univ : Finset (D.fresh.Pool C)).Nonempty from ⟨d C, Finset.mem_univ _⟩)
  have hiid : D.encoding.iidLaw = FinLaw.pi P := uniform_pi d
  rw [LateData.cellPoolLaw, hiid, map_pi_coordinate P d C]
  change FinLaw.uniform Finset.univ ⟨d C, Finset.mem_univ _⟩ =
    FinLaw.pi (fun _ : Fin (D.geom.nslot C) => FinLaw.uniform Finset.univ hBins)
  exact uniform_pi (d C)

theorem pr_compl_add {A : Type*} [Fintype A] (P : FinLaw A) (f : A → Prop) :
    P.pr f + P.pr (fun a => ¬ f a) = 1 := by
  classical
  unfold FinLaw.pr
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ a, P.w a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a <;> simp [ha]
    _ = 1 := P.sum_one

theorem map_pr {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (e : A → B) (f : B → Prop) :
    (FinLaw.map P e).pr f = P.pr (fun a => f (e a)) := by
  classical
  unfold FinLaw.pr FinLaw.map
  change (∑ b, if f b then ∑ a, if e a = b then P.w a else 0 else 0) = _
  have hterm (b : B) : (if f b then ∑ a, if e a = b then P.w a else 0 else 0) =
      ∑ a, if e a = b ∧ f b then P.w a else 0 := by
    by_cases hb : f b <;> simp [hb]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (e a)]
  · simp
  · intro b _ hb; simp [hb, eq_comm]
  · simp

theorem source_slice_mass {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hκ : κ.Admissible) (hPT : PT.Valid)
    {G : LowGeom PT} (R : S16.Lane_sol_fix2_s16.CellRawData G) (hR : R.SourceValid)
    (C : G.Cell) (s : R.Slice C) :
    1 - (0.00001 : ℝ) ≤ ∑ W ∈ R.slicePass C s, (R.sliceLaw C s).w W := by
  classical
  rcases hR with ⟨hm, hUniform, hSource⟩ | ⟨hc, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    have hprob : (R.sliceLaw C s).pr (fun W => W ∈ R.slicePass C s) =
        (S.recLaw PT.parameter).pr S.AllGood := by
      rw [hLaw, map_pr]
      congr 1
      funext W
      apply propext
      simpa only [Equiv.apply_symm_apply] using hPass s ((records s).symm W)
    have hBad : (S.recLaw PT.parameter).pr (fun W => ¬ S.AllGood W) ≤
        Real.exp (-Real.rpow ((PT.tiling.P (G.cellPatch C)).h : ℝ) (1 + κ.c14)) := by
      simpa [SliceSolver.AllGood, SliceSolver.recLaw] using S.Hgood_bad PT.parameter
    have hComp := pr_compl_add (S.recLaw PT.parameter) S.AllGood
    have hErr := (patch_rate_and_error hκ hPT hm (G.cellPatch C)).2
    have hExp : Real.exp (-Real.rpow ((PT.tiling.P (G.cellPatch C)).h : ℝ) (1 + κ.c14)) ≤
        0.00001 := by
      nlinarith [show (0 : ℝ) ≤ 2 * (PT.tiling.P (G.cellPatch C)).h ^ 2 *
        Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) by positivity]
    have hMass : 1 - (0.00001 : ℝ) ≤ (R.sliceLaw C s).pr (fun W => W ∈ R.slicePass C s) := by
      rw [hprob]
      linarith
    have heq : (R.sliceLaw C s).pr (fun W => W ∈ R.slicePass C s) =
        ∑ W ∈ R.slicePass C s, (R.sliceLaw C s).w W := by
      unfold FinLaw.pr
      calc
        _ = ∑ W, if W ∈ R.slicePass C s then (R.sliceLaw C s).w W else 0 := by
          apply Finset.sum_congr rfl
          intro W _
          by_cases hw : W ∈ R.slicePass C s <;> simp [hw]
        _ = _ := by
          rw [← Finset.sum_filter]
          congr 1
          ext W
          simp
    rw [heq] at hMass
    exact hMass
  · have hPass : R.slicePass C s = Finset.univ := (hSource C).2.2.1 s
    rw [hPass, (R.sliceLaw C s).sum_one]
    norm_num

theorem source_cluster_conditioned_queries {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (hκ : κ.Admissible) (hPT : PT.Valid)
    (R : S16.Lane_sol_fix2_s16.CellRawData G) (hR : R.SourceValid)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) {A : Type*} [Fintype A] [DecidableEq A]
    (r : A → S16.OddCellRole G C) (f : A → Fin (T.S.N k) → ℝ) (hf : ∀ a y, 0 ≤ f a y)
    (hMargin : 2 < 20 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ)) :
    (R.history C).E (fun W => ∏ a, rawQueryMoment R C (r a) W (f a)) ≤
      (1 - (0.00001 : ℝ))⁻¹ ^ Fintype.card A *
        ∏ a, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y := by
  classical
  obtain ⟨hm, hUniform, hSource⟩ := hR.resolve_right (fun h => h.1 hc)
  obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
  let loc := fun a => (R.cellWords C).symm ⟨(r a).1, (r a).2.1⟩
  let c := fun a => (loc a).1
  let SS := Finset.univ.image c
  let ψ := fun a W => solverQueryMoment S (S.groupOf (loc a).2) W (f a)
  let test (s : R.Slice C) (W : R.Value C s) :=
    ∏ a : {a : A // c a = s}, ψ a.1 (records s W)
  have epos (a : A) : (R.cellWords C (loc a)).1 = (r a).1 :=
    congrArg Subtype.val ((R.cellWords C).apply_symm_apply _)
  have hGrp (a : A) : R.groupOf C (r a) = groups ((loc a).1, S.groupOf (loc a).2) := by
    have ho : ¬ IsEvenRole (R.cellWords C (loc a)).1 := by rw [epos]; exact (r a).2.2
    have h := hGroup (loc a).1 (loc a).2 ho
    have he : (⟨(R.cellWords C (loc a)).1, (R.cellWords C (loc a)).2, ho⟩ : S16.OddCellRole G C) = r a :=
      Subtype.ext (epos a)
    rw [he] at h
    exact h
  have hMoment (a : A) (W : R.Hist C) :
      rawQueryMoment R C (r a) W (f a) = ψ a (records (c a) (W (c a))) := by
    unfold rawQueryMoment
    rw [hGrp]
    apply Finset.sum_congr rfl
    intro b _
    rw [hQ]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    rw [hU]
  have hpoint (W : R.Hist C) : (∏ a, rawQueryMoment R C (r a) W (f a)) =
      ∏ s ∈ SS, test s (W s) := by
    simp_rw [hMoment]
    rw [← prod_fibres c SS (fun a => Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)]
    apply Finset.prod_congr rfl
    intro s _
    apply Finset.prod_congr rfl
    intro a _
    rw [a.2]
  have htest : ∀ s W, 0 ≤ test s W := fun s W => Finset.prod_nonneg (fun a _ =>
    solver_query_nonneg S _ _ (f a.1) (hf a.1))
  have hcond := conditioned_prod_bound (R.sliceLaw C) (R.slicePass C) (R.slice_pos C)
    0.00001 (by norm_num) (source_slice_mass hκ hPT R hR C) SS test htest
  have hcard : SS.card ≤ Fintype.card A := Finset.card_image_le.trans (by simp)
  have hcost : (1 - (0.00001 : ℝ))⁻¹ ^ SS.card ≤
      (1 - (0.00001 : ℝ))⁻¹ ^ Fintype.card A := pow_le_pow_right₀ (by norm_num) hcard
  have hRaw := source_cluster_raw_factorization hPT R hR hc C r f hMargin hSep
  have hprod : 0 ≤ ∏ a, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y :=
    Finset.prod_nonneg (fun a _ => Finset.sum_nonneg (fun y _ =>
      mul_nonneg ((PT.πraw _).nonneg y) (hf a y)))
  calc
    _ = (R.history C).E (fun W => ∏ s ∈ SS, test s (W s)) := by simp_rw [hpoint]
    _ ≤ (1 - (0.00001 : ℝ))⁻¹ ^ SS.card *
        (R.rawHistory C).E (fun W => ∏ s ∈ SS, test s (W s)) := hcond
    _ = (1 - (0.00001 : ℝ))⁻¹ ^ SS.card *
        (R.rawHistory C).E (fun W => ∏ a, rawQueryMoment R C (r a) W (f a)) := by simp_rw [hpoint]
    _ = (1 - (0.00001 : ℝ))⁻¹ ^ SS.card *
        ∏ a, ∑ y, (PT.πraw (G.cellPatch C)).w y * f a y := by rw [hRaw]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost hprod

end HypercubeRamsey.S18.Lane_sol_d18l_cal
