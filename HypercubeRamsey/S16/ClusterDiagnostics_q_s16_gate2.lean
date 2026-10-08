import HypercubeRamsey.S16.ProducersDefs

namespace HypercubeRamsey.S16.Lane_q_s16_gate2

open Classical
open scoped BigOperators
open HypercubeRamsey.S16.Lane_sol_fix2_s16

private theorem finLaw_ext {α : Type*} [Fintype α] {P Q : FinLaw α}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P with
  | mk pw hp hs =>
    cases Q with
    | mk qw hq hsq =>
      have hw : pw = qw := funext h
      subst qw
      rfl

/-- Mapping a product law coordinatewise gives the product of the image laws. -/
private theorem finLaw_map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} {β : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (P : ∀ i, FinLaw (α i)) (f : ∀ i, α i → β i) :
    FinLaw.map (FinLaw.pi P) (fun x i => f i (x i)) =
      FinLaw.pi (fun i => FinLaw.map (P i) (f i)) := by
  classical
  apply finLaw_ext
  intro y
  simp only [FinLaw.map, FinLaw.pi]
  calc
    (∑ x : (∀ i, α i),
        if (fun i => f i (x i)) = y then ∏ i, (P i).w (x i) else 0) =
        ∑ x : (∀ i, α i), ∏ i, if f i (x i) = y i then (P i).w (x i) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hall : ∀ i, f i (x i) = y i
      · have hfun : (fun i => f i (x i)) = y := funext hall
        simp [hfun, hall]
      · have hex : ∃ i, f i (x i) ≠ y i := by
          simpa only [not_forall] using hall
        obtain ⟨i, hi⟩ := hex
        have hfun : (fun i => f i (x i)) ≠ y := by
          intro heq
          exact hi (congrFun heq i)
        rw [if_neg hfun]
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hi]
    _ = ∏ i, ∑ a : α i, if f i a = y i then (P i).w a else 0 :=
      (Fintype.prod_sum (fun i a => if f i a = y i then (P i).w a else 0)).symm
    _ = ∏ i, (FinLaw.map (P i) (f i)).w (y i) := by
      simp [FinLaw.map]

/-- The conditioned law, represented on its positive support subtype. -/
private noncomputable def condSupportLaw {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (A : Finset α) (hA : 0 < ∑ x ∈ A, P.w x) :
    FinLaw {x : α // x ∈ A ∧ P.w x ≠ 0} := by
  classical
  let Q := FinLaw.cond P A hA
  let p := fun x : α => x ∈ A ∧ P.w x ≠ 0
  refine ⟨fun z => Q.w z.1, ?_, ?_⟩
  · intro z
    exact Q.nonneg z.1
  · have hfilter :
        (∑ z : {x : α // p x}, Q.w z.1) =
          ∑ x ∈ Finset.univ.filter p, Q.w x := by
      simpa [p] using
        (Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset α))
          (p := p) (f := fun x => Q.w x))
    have hsub : Finset.univ.filter p ⊆ A := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx.1
    have hzero : ∀ x ∈ A, x ∉ Finset.univ.filter p → Q.w x = 0 := by
      intro x hxA hxnot
      have hnot : ¬ p x := by
        intro hp
        apply hxnot
        simp [hp]
      rcases not_and_or.mp hnot with hnotA | hzero
      · exact (hnotA hxA).elim
      · have hPx : P.w x = 0 := not_ne_iff.mp hzero
        simp [Q, FinLaw.cond, hxA, hPx]
    have hQsum : (∑ x ∈ A, Q.w x) = 1 := by
      calc
        (∑ x ∈ A, Q.w x) = (∑ x ∈ A, P.w x) / (∑ x ∈ A, P.w x) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro x hx
          simp [Q, FinLaw.cond, hx]
        _ = 1 := div_self (ne_of_gt hA)
    calc
      (∑ z : {x : α // p x}, Q.w z.1) = ∑ x ∈ Finset.univ.filter p, Q.w x := hfilter
      _ = ∑ x ∈ A, Q.w x := Finset.sum_subset hsub hzero
      _ = 1 := hQsum

private theorem condSupport_map {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (A : Finset α) (hA : 0 < ∑ x ∈ A, P.w x) :
    FinLaw.map (condSupportLaw P A hA)
        (fun z : {x : α // x ∈ A ∧ P.w x ≠ 0} => z.1) = FinLaw.cond P A hA := by
  classical
  apply finLaw_ext
  intro x
  let p := fun a : α => a ∈ A ∧ P.w a ≠ 0
  change (∑ z : {a : α // p a},
      if z.1 = x then (FinLaw.cond P A hA).w z.1 else 0) =
    (FinLaw.cond P A hA).w x
  by_cases hx : p x
  · rw [Finset.sum_eq_single (⟨x, hx⟩ : {a : α // p a})]
    · simp
    · intro z hz hne
      have hval : z.1 ≠ x := by
        intro heq
        exact hne (Subtype.ext heq)
      simp [hval]
    · simp
  · have hzero : (FinLaw.cond P A hA).w x = 0 := by
      rcases not_and_or.mp hx with hnotA | hweight
      · simp [FinLaw.cond, hnotA]
      · have hz : P.w x = 0 := not_ne_iff.mp hweight
        simp [FinLaw.cond, hz]
    rw [hzero]
    apply Finset.sum_eq_zero
    intro z hz
    have hval : z.1 ≠ x := by
      intro heq
      subst x
      exact hx ⟨z.property.1, z.property.2⟩
    simp [hval]

/-- Product conditioning is the image of the product of positive-support laws. -/
theorem pi_cond_support_map {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (P : ∀ i, FinLaw (V i)) (A : ∀ i, Finset (V i))
    (hA : ∀ i, 0 < ∑ v ∈ A i, (P i).w v) :
    ∃ P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0},
      FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) := by
  classical
  let P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0} :=
    fun i => condSupportLaw (P i) (A i) (hA i)
  refine ⟨P', ?_⟩
  calc
    FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.pi (fun i => FinLaw.map (P' i) (fun z => z.1)) := by
      congr 1
      funext i
      exact (condSupport_map (P i) (A i) (hA i)).symm
    _ = FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) :=
      (finLaw_map_pi P' (fun i z => z.1)).symm

private theorem history_support_iff {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (C : G.Cell) (W : R.Hist C) :
    (R.history C).w W ≠ 0 ↔
      ∀ s, W s ∈ R.slicePass C s ∧ (R.sliceLaw C s).w (W s) ≠ 0 := by
  classical
  constructor
  · intro hW s
    exact Lane_sol_s16_prod1.cond_support _ _ _ _
      (Lane_sol_s16_prod1.pi_support _ W hW s)
  · intro hW
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    simp only [FinLaw.cond, if_pos (hW s).1]
    exact div_ne_zero (hW s).2 (R.slice_pos C s).ne'

private theorem cluster_qin_row_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (C : G.Cell) (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
    (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (hQ : ∀ W s g b, (R.qraw C W (groups (s, g))).w b = S.q g (records s (W s)) b)
    (hTrim : ∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (s : R.Slice C) (g : HypercubeRamsey.Group PT.tiling (G.cellPatch C))
    (heq : W s = W' s) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W (groups (s, g))).w b = (R.qin C W' (groups (s, g))).w b := by
  rw [R.qin_eq C W _ b ((history_support_iff R C W).mp hW),
    R.qin_eq C W' _ b ((history_support_iff R C W').mp hW')]
  simp_rw [hTrim, hQ, heq]

private theorem cluster_qbar_row_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (C : G.Cell) (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
    (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (hQ : ∀ W s g b, (R.qraw C W (groups (s, g))).w b = S.q g (records s (W s)) b)
    (hTrim : ∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (s : R.Slice C) (g : HypercubeRamsey.Group PT.tiling (G.cellPatch C))
    (heq : W s = W' s) (b : Bin PT.tiling (G.cellPatch C)) :
    (K.qbar C W (groups (s, g))).w b = (K.qbar C W' (groups (s, g))).w b := by
  rw [K.qbar_eq C W _ b hW, K.qbar_eq C W' _ b hW']
  simp_rw [cluster_qin_row_local R C S records groups hQ hTrim W W' hW hW' s g heq]

/-- One odd role's restricted load summand is determined by its own slice value. -/
theorem cluster_role_term_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hFallback : ∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
      K.qtilde C pool W g = K.qbar C W g)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (pool : CellPool G C)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (r : OddCellRole G C)
    (heq : W ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1 =
      W' ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1)
    (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y =
      ∑ b, (K.qtilde C pool W' (R.groupOf C r)).w b * (R.U C W' (R.groupOf C r) b).w y := by
  classical
  rcases hR with ⟨_, _, hSource⟩ | ⟨hDirect, _⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let sz : R.Slice C × IWord PT.tiling (G.cellPatch C) :=
      (R.cellWords C).symm ⟨r.1, r.2.1⟩
    have hpos : (R.cellWords C sz).1 = r.1 := by
      simpa [sz] using congrArg Subtype.val
        ((R.cellWords C).apply_symm_apply ⟨r.1, r.2.1⟩)
    have hodd : ¬ IsEvenRole (R.cellWords C sz).1 := by
      intro hEven
      exact r.2.2 (hpos ▸ hEven)
    have hoddWord : ¬ IsEvenRole sz.2 := by
      intro hEven
      exact hodd ((R.word_parity hc C sz.1 sz.2).mpr hEven)
    let r' : OddCellRole G C := ⟨(R.cellWords C sz).1, (R.cellWords C sz).2, hodd⟩
    have hr' : r' = r := Subtype.ext hpos
    have hgroup : R.groupOf C r = groups (sz.1, S.groupOf sz.2) := by
      calc
        R.groupOf C r = R.groupOf C r' := by rw [hr']
        _ = groups (sz.1, S.groupOf sz.2) := hGroup sz.1 sz.2 hodd
    change W sz.1 = W' sz.1 at heq
    have hbar : ∀ b, (K.qbar C W (R.groupOf C r)).w b =
        (K.qbar C W' (R.groupOf C r)).w b := by
      intro b
      rw [hgroup]
      exact cluster_qbar_row_local R Perm K C S records groups hQ hTrim
        W W' hW hW' sz.1 (S.groupOf sz.2) heq b
    have hmass :
        (∑ b ∈ Finset.univ.image pool, (K.qbar C W (R.groupOf C r)).w b) =
          ∑ b ∈ Finset.univ.image pool, (K.qbar C W' (R.groupOf C r)).w b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact hbar b
    have hqtilde : ∀ b,
        (K.qtilde C pool W (R.groupOf C r)).w b =
          (K.qtilde C pool W' (R.groupOf C r)).w b := by
      intro b
      by_cases hm :
          (∑ b ∈ Finset.univ.image pool, (K.qbar C W (R.groupOf C r)).w b) ≠ 0
      · have hm' :
            (∑ b ∈ Finset.univ.image pool, (K.qbar C W' (R.groupOf C r)).w b) ≠ 0 := by
          rw [← hmass]
          exact hm
        rw [K.qtilde_eq C pool W (R.groupOf C r) b hW hm,
          K.qtilde_eq C pool W' (R.groupOf C r) b hW' hm', hbar b, hmass]
      · have hz :
            (∑ b ∈ Finset.univ.image pool, (K.qbar C W (R.groupOf C r)).w b) = 0 :=
          not_ne_iff.mp hm
        have hz' :
            (∑ b ∈ Finset.univ.image pool, (K.qbar C W' (R.groupOf C r)).w b) = 0 := by
          rw [← hmass]
          exact hz
        rw [hFallback C pool W (R.groupOf C r) hz,
          hFallback C pool W' (R.groupOf C r) hz', hbar b]
    have hUrow : ∀ b,
        (R.U C W (R.groupOf C r) b).w y =
          (R.U C W' (R.groupOf C r) b).w y := by
      intro b
      rw [hgroup]
      calc
        (R.U C W (groups (sz.1, S.groupOf sz.2)) b).w y =
            S.U (S.groupOf sz.2) (records sz.1 (W sz.1)) b y := hU W sz.1 (S.groupOf sz.2) b y
        _ = S.U (S.groupOf sz.2) (records sz.1 (W' sz.1)) b y := by rw [heq]
        _ = (R.U C W' (groups (sz.1, S.groupOf sz.2)) b).w y :=
            (hU W' sz.1 (S.groupOf sz.2) b y).symm
    calc
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y =
          ∑ b, (K.qtilde C pool W' (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hqtilde b]
      _ = ∑ b, (K.qtilde C pool W' (R.groupOf C r)).w b *
            (R.U C W' (R.groupOf C r) b).w y := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [hUrow b]
  · exact (hDirect hc).elim

private theorem physical_bin_count {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {K16 : ℝ} (hκ : κ.Admissible)
    (Q : LowModeQuantFacts hκ (PT := PT) K16)
    (i : Fin PT.tiling.m) :
    (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d = (PT.tiling.P i).M := by
  have h := (PT.tiling.P i).bins.sum_card_parts
  have he : ∑ b ∈ (PT.tiling.P i).bins.parts, b.card =
      (PT.tiling.P i).bins.parts.card * (PT.tiling.P i).d := by
    calc
      _ = ∑ b ∈ (PT.tiling.P i).bins.parts, (PT.tiling.P i).d :=
        Finset.sum_congr rfl (fun b hb => Q.profiled_valid.tiling_valid.bins_card i b hb)
      _ = _ := by simp
  rw [he, (PT.tiling.P i).cardY] at h
  have hn : Fintype.card (Bin PT.tiling i) * (PT.tiling.P i).d = (PT.tiling.P i).M := by
    change Fintype.card {b // b ∈ (PT.tiling.P i).bins.parts} * (PT.tiling.P i).d = _
    rw [Fintype.card_of_subtype (PT.tiling.P i).bins.parts (fun _ => Iff.rfl)]
    exact h
  exact_mod_cast hn

private theorem cluster_incoming_bound {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
    (R : CellRawData G) (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (C : G.Cell) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (g : R.Group C) (b : Bin PT.tiling (G.cellPatch C)) :
    (R.qin C W g).w b ≤
      8 * Real.exp (2 * (sliceK κ (PT.tiling.P (G.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (G.cellPatch C)).h) /
        Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
  classical
  have hB : (0 : ℝ) < Fintype.card (Bin PT.tiling (G.cellPatch C)) := by
    have hne : Nonempty (Bin PT.tiling (G.cellPatch C)) := by
      by_contra hn
      letI : IsEmpty (Bin PT.tiling (G.cellPatch C)) := not_nonempty_iff.mp hn
      have hh := (R.qin C W g).sum_one
      simp at hh
    letI := hne
    exact_mod_cast Fintype.card_pos
  rcases hR with ⟨hMode, _, hSource⟩ | ⟨hDirect, _⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    obtain ⟨⟨ss, g'⟩, hsg⟩ := groups.surjective g
    have hg : S.AllGood (records ss (W ss)) :=
      (hPass ss (W ss)).mp ((history_support_iff R C W).mp hW ss).1
    have hqin : (R.qin C W g).w b = S.qin (records ss (W ss)) g' b := by
      rw [← hsg, R.qin_eq C W _ b ((history_support_iff R C W).mp hW), hTrim]
      simp_rw [hQ]
      unfold SliceSolver.qin
      split_ifs <;> simp
    rw [hqin]
    have hcap := Lane_sol_s16_prod1.solver_qin_cap S (records ss (W ss)) hg g' b
      (Lane_sol_s16_prod1.low_cluster_pretrim_small hκ Q hMode (G.cellPatch C))
    have hM := physical_bin_count hκ Q (G.cellPatch C)
    have hdpos : (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).d := by
      have hMpos : (0 : ℝ) < (PT.tiling.P (G.cellPatch C)).M := by
        rw [← (PT.tiling.P (G.cellPatch C)).cardY]
        exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty _).2
      nlinarith
    apply hcap.trans
    rw [← hM]
    simp only [Tiling.kScale, Tiling.tScale]
    field_simp [hB.ne', hdpos.ne']
    norm_num
  · exact (hDirect hc).elim

private theorem physical_bins_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m)
    (b b' : Bin PT.tiling i) (hne : b ≠ b') : Disjoint b.1 b'.1 := by
  exact (PT.tiling.P i).bins.disjoint b.2 b'.2
    (fun h => hne (Subtype.ext h))

/-- The qin and qbar atom estimates, followed by the pool restriction, bound
one qtilde atom by `32 exp(2kT) / L`. Disjoint physical bins make each label
receive mass from at most one bin. -/
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
  classical
  let i := H.geom.cellPatch C
  let L : ℝ := H.geom.nslot C
  let B : ℝ := Fintype.card (Bin PT.tiling i)
  let E : ℝ := Real.exp (2 * (sliceK κ (PT.tiling.P i).h : ℝ) * sliceT κ (PT.tiling.P i).h)
  have hB : 0 < B := by
    dsimp [B]
    letI := (hPerm C W hW).bins_nonempty
    exact_mod_cast Fintype.card_pos
  have hM := physical_bin_count hκ Q i
  have hMpos : (0 : ℝ) < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardY]
    exact_mod_cast Finset.card_pos.mpr (Q.profiled_valid.tiling_valid.patch_nonempty i).2
  have hdpos : (0 : ℝ) < (PT.tiling.P i).d := by
    have hBmul : B * (PT.tiling.P i).d = (PT.tiling.P i).M := by
      change (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d = _
      exact hM
    have hdiv := div_pos hMpos hB
    rw [← hBmul] at hdiv
    simpa [hB.ne'] using hdiv
  have hnpos : (0 : ℝ) < T.S.n k := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) Q.n_large
  have hKpos : 0 < κ.Kcell := lt_of_lt_of_le
    (div_pos (by norm_num) hκ.bucket.2.2.2.2) hκ.Kcell_big
  have hL : 0 < L := by
    have hslots := H.cell_partition.slot_count C
    change H.geom.nslot C =
      ⌈κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / (PT.tiling.P i).d⌉₊ at hslots
    have harg : 0 < κ.Kcell * Real.rpow (T.S.n k : ℝ) κ.Ac / (PT.tiling.P i).d :=
      div_pos (mul_pos hKpos (Real.rpow_pos_of_pos hnpos _)) hdpos
    have hLnat : 0 < H.geom.nslot C := by
      rw [hslots]
      exact_mod_cast lt_of_lt_of_le harg (Nat.le_ceil _)
    simpa [L] using hLnat
  have hqinCap : ∀ g b, (R.qin C W g).w b ≤ 8 * E / B := by
    intro g b
    simpa [i, E, B] using cluster_incoming_bound hκ Q R hR hc C W hW g b
  have hret : (1 / 2 : ℝ) ≤
      ∑ b ∈ (Perm.table C).permitted (R.groupOf C r), (R.qin C W (R.groupOf C r)).w b :=
    Lane_sol_s16_prod1.permission_retained_half (Perm.table C) (R.qin C W)
      (hPerm C W hW) (R.groupOf C r)
  have hbar : ∀ b, (K.qbar C W (R.groupOf C r)).w b ≤ 16 * E / B := by
    intro b
    rw [K.qbar_eq C W (R.groupOf C r) b hW]
    by_cases hb : b ∈ (Perm.table C).permitted (R.groupOf C r)
    · rw [if_pos hb]
      calc
        _ ≤ (8 * E / B) /
            (∑ b ∈ (Perm.table C).permitted (R.groupOf C r),
              (R.qin C W (R.groupOf C r)).w b) :=
          div_le_div_of_nonneg_right (hqinCap _ _) (by linarith)
        _ ≤ (8 * E / B) / (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hret
        _ = 16 * E / B := by ring
    · rw [if_neg hb]
      simp only [zero_div]
      positivity
  have hlower : L / (2 * B) ≤
      ∑ b ∈ Finset.univ.image pool, (K.qbar C W (R.groupOf C r)).w b := by
    calc
      L / (2 * B) = (1 / 2) * (L / B) := by ring
      _ ≤ (1 - Real.rpow (T.S.n k : ℝ) (-4)) * (L / B) :=
        mul_le_mul_of_nonneg_right (by linarith [hn4]) (div_nonneg hL.le hB.le)
      _ ≤ _ := by simpa only [L, B] using hmass (R.groupOf C r)
  have hnorm :
      (∑ b ∈ Finset.univ.image pool, (K.qbar C W (R.groupOf C r)).w b) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (div_pos hL (mul_pos (by norm_num) hB)) hlower)
  have hpoolCap : ∀ b,
      (K.qtilde C pool W (R.groupOf C r)).w b ≤ 32 * E / L := by
    intro b
    have hcap := Lane_sol_s16_prod1.pool_atom_cap
      (K.qbar C W (R.groupOf C r)) (K.qtilde C pool W (R.groupOf C r))
      (Finset.univ.image pool) L B (16 * E) hL hB (by positivity) hbar hlower
      (fun b => K.qtilde_eq C pool W (R.groupOf C r) b hW hnorm)
    have hb := hcap b
    change (K.qtilde C pool W (R.groupOf C r)).w b ≤ 2 * (16 * E) / L at hb
    calc
      (K.qtilde C pool W (R.groupOf C r)).w b ≤ 2 * (16 * E) / L := hb
      _ = 32 * E / L := by ring
  let Bs : Finset (Bin PT.tiling i) := Finset.univ.filter fun b => y ∈ b.1
  have hBs : Bs.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    by_contra hne
    exact Finset.disjoint_left.mp (physical_bins_disjoint i b b' hne)
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2
  have hUle : ∀ b, (R.U C W (R.groupOf C r) b).w y ≤ 1 := by
    intro b
    calc
      (R.U C W (R.groupOf C r) b).w y ≤
          ∑ y', (R.U C W (R.groupOf C r) b).w y' :=
        Finset.single_le_sum (fun y' _ => (R.U C W (R.groupOf C r) b).nonneg y')
          (Finset.mem_univ y)
      _ = 1 := (R.U C W (R.groupOf C r) b).sum_one
  have hsumFilter :
      (∑ b, (K.qtilde C pool W (R.groupOf C r)).w b *
        (R.U C W (R.groupOf C r) b).w y) =
        ∑ b ∈ Bs, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w y := by
    symm
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hy : y ∈ b.1
    · simp [Bs, hy]
    · have hzero : (R.U C W (R.groupOf C r) b).w y = 0 := by
        by_contra hz
        exact hy (R.U_support C W (R.groupOf C r) b y hz)
      simp [Bs, hy, hzero]
  have hsumCap :
      (∑ b ∈ Bs, (K.qtilde C pool W (R.groupOf C r)).w b *
        (R.U C W (R.groupOf C r) b).w y) ≤ 32 * E / L := by
    calc
      _ ≤ ∑ b ∈ Bs, (32 * E / L) := by
        apply Finset.sum_le_sum
        intro b hb
        calc
          (K.qtilde C pool W (R.groupOf C r)).w b *
              (R.U C W (R.groupOf C r) b).w y ≤
          (K.qtilde C pool W (R.groupOf C r)).w b * 1 :=
              mul_le_mul_of_nonneg_left (hUle b) ((K.qtilde C pool W (R.groupOf C r)).nonneg b)
          _ ≤ 32 * E / L := by simpa using hpoolCap b
      _ = (Bs.card : ℝ) * (32 * E / L) := by simp
      _ ≤ 32 * E / L := by
        have hcard : (Bs.card : ℝ) ≤ 1 := by exact_mod_cast hBs
        have hnonneg : 0 ≤ 32 * E / L := by positivity
        calc
          (Bs.card : ℝ) * (32 * E / L) ≤ 1 * (32 * E / L) :=
            mul_le_mul_of_nonneg_right hcard hnonneg
          _ = 32 * E / L := by ring
  calc
    _ = ∑ b ∈ Bs, (K.qtilde C pool W (R.groupOf C r)).w b *
          (R.U C W (R.groupOf C r) b).w y := hsumFilter
    _ ≤ 32 * E / L := hsumCap
    _ ≤ 64 * E / L := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (32 : ℝ) ≤ 64) (Real.exp_pos _).le) hL.le

end HypercubeRamsey.S16.Lane_q_s16_gate2
