import HypercubeRamsey.S18.Nodes_sol_s18_2lm_moments
import HypercubeRamsey.S18.Nodes_q_s18_n2
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.Blocks

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

/-- Product-law independence of events reading disjoint coordinate sets. -/
theorem pi_pr_and {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (Q : ∀ i, FinLaw (Ω i))
    (A B : (∀ i, Ω i) → Prop) (S V : Finset I)
    (hA : ∀ s s', (∀ i ∈ S, s i = s' i) → (A s ↔ A s'))
    (hB : ∀ s s', (∀ i ∈ V, s i = s' i) → (B s ↔ B s'))
    (hdis : Disjoint S V) :
    (FinLaw.pi Q).pr (fun s => A s ∧ B s) =
      (FinLaw.pi Q).pr A * (FinLaw.pi Q).pr B := by
  classical
  let P : ∀ i, FinProb (Ω i) := fun i => ⟨(Q i).w, (Q i).nonneg, (Q i).sum_one⟩
  have h := FinProb.pi_expect_mul_of_disjoint P
    (fun s => if A s then 1 else 0) (fun s => if B s then 1 else 0) S V
    (by intro s s' he; simp only [hA s s' he])
    (by intro s s' he; simp only [hB s s' he]) hdis
  have hprod (s : ∀ i, Ω i) :
      (if A s then (1 : ℝ) else 0) * (if B s then 1 else 0) =
        (if A s ∧ B s then 1 else 0) := by
    by_cases ha : A s <;> by_cases hb : B s <;> simp [ha, hb]
  simpa only [FinProb.expect, FinProb.pi, P, hprod,
    mul_ite, mul_one, mul_zero, FinLaw.pr, FinLaw.pi] using h

/-- A finite family of block events factors without duplicating equivalent
blocks. This applies to both raw cylinders and their survival intersections. -/
theorem pi_pr_all_disjoint {I J : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (Q : ∀ i, FinLaw (Ω i))
    (A : J → (∀ i, Ω i) → Prop) (S : J → Finset I) (F : Finset J)
    (hA : ∀ j ∈ F, ∀ s s', (∀ i ∈ S j, s i = s' i) → (A j s ↔ A j s'))
    (hdis : ∀ j ∈ F, ∀ j' ∈ F, j ≠ j' → Disjoint (S j) (S j')) :
    (FinLaw.pi Q).pr (fun s => ∀ j ∈ F, A j s) =
      ∏ j ∈ F, (FinLaw.pi Q).pr (A j) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [FinLaw.pr, (FinLaw.pi Q).sum_one]
  | @insert j F hj ih =>
    have hdisj : Disjoint (S j) (F.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro i hi hmem
      obtain ⟨j', hj', hi'⟩ := Finset.mem_biUnion.mp hmem
      exact Finset.disjoint_left.mp (hdis j (by simp) j' (by simp [hj'])
        (by intro he; exact hj (he ▸ hj'))) hi hi'
    have hdep : ∀ s s', (∀ i ∈ F.biUnion S, s i = s' i) →
        ((∀ j' ∈ F, A j' s) ↔ ∀ j' ∈ F, A j' s') := by
      intro s s' he
      apply forall₂_congr
      intro j' hj'
      exact hA j' (by simp [hj']) s s' (fun i hi => he i (Finset.mem_biUnion.mpr ⟨j', hj', hi⟩))
    have hsplit := pi_pr_and Q (A j) (fun s => ∀ j' ∈ F, A j' s)
      (S j) (F.biUnion S) (hA j (by simp)) hdep hdisj
    have hevent : (fun s => ∀ j' ∈ insert j F, A j' s) =
        (fun s => A j s ∧ ∀ j' ∈ F, A j' s) := by
      funext s
      apply propext
      simp
    rw [hevent, hsplit, ih
      (fun j' hj' => hA j' (by simp [hj']))
      (fun j' hj' j'' hj'' => hdis j' (by simp [hj']) j'' (by simp [hj'']))]
    simp [hj]

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

theorem sameBlock_refl (a : Fin (T.S.n k)) : X.sameBlock a a := by
  unfold CriticalTransferData.sameBlock
  exact Or.inl (by simp)

theorem blockCells_eq {a b : Fin (T.S.n k)} (h : X.sameBlock a b) :
    X.blockCells a = X.blockCells b := by
  have hf : ∀ u, X.sameBlock a u ↔ X.sameBlock b u := by
    intro u
    exact ⟨fun hu => Lane_q_s18_n2.sameBlock_trans
      (Lane_q_s18_n2.sameBlock_symm h) hu,
      fun hu => Lane_q_s18_n2.sameBlock_trans h hu⟩
  simp only [CriticalTransferData.blockCells, hf]

/-- Least representatives of the equivalence classes of responding blocks. -/
noncomputable def representatives (X : CriticalTransferData D) : Finset (Fin (T.S.n k)) :=
  Finset.univ.filter fun a => ∀ b, X.sameBlock a b → a ≤ b

theorem representative_exists (a : Fin (T.S.n k)) :
    ∃ b ∈ representatives X, X.sameBlock b a := by
  let F := Finset.univ.filter (X.sameBlock a)
  have hF : F.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, sameBlock_refl a⟩⟩
  let b := F.min' hF
  have hb : X.sameBlock a b := (Finset.mem_filter.mp (Finset.min'_mem F hF)).2
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
    Lane_q_s18_n2.sameBlock_symm hb⟩
  intro u hu
  exact Finset.min'_le F u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    Lane_q_s18_n2.sameBlock_trans hb hu⟩)

theorem representatives_not_same {a b : Fin (T.S.n k)}
    (ha : a ∈ representatives X) (hb : b ∈ representatives X) (hne : a ≠ b) :
    ¬ X.sameBlock a b := by
  intro h
  exact hne (le_antisymm ((Finset.mem_filter.mp ha).2 b h)
    ((Finset.mem_filter.mp hb).2 a (Lane_q_s18_n2.sameBlock_symm h)))

theorem blockCells_disjoint (hgeom : TransferGeometry X) {a b : Fin (T.S.n k)}
    (hab : ¬ X.sameBlock a b) : Disjoint (X.blockCells a) (X.blockCells b) := by
  apply Finset.disjoint_left.mpr
  intro C hCa hCb
  obtain ⟨u, hu, heU⟩ := Finset.mem_image.mp hCa
  obtain ⟨v, hv, heV⟩ := Finset.mem_image.mp hCb
  obtain ⟨hucrit, hau⟩ := Finset.mem_filter.mp hu
  obtain ⟨hvcrit, hbv⟩ := Finset.mem_filter.mp hv
  have huv := hgeom.distinct_cells u hucrit v hvcrit (heU.trans heV.symm)
  subst v
  exact hab (Lane_q_s18_n2.sameBlock_trans hau (Lane_q_s18_n2.sameBlock_symm hbv))

/-- The canonical transcript cylinder for one equivalence class. It lists
only those answer checks whose requests belong to that class. -/
noncomputable def cylinder (P : TransferProtocol X) (seed : P.Seed)
    (s : X.Raw) (t : ℕ) (a : Fin (T.S.n k)) (u : X.Raw) : Prop :=
  ∀ j, j < t → X.sameBlock a (P.request seed (P.replies seed s j)) →
    P.answer seed (P.replies seed s j) u = P.answer seed (P.replies seed s j) s

theorem cylinder_local (P : TransferProtocol X) (seed : P.Seed)
    (s : X.Raw) (t : ℕ) (a : Fin (T.S.n k)) (u u' : X.Raw)
    (he : ∀ C ∈ X.blockCells a, u C = u' C) :
    cylinder P seed s t a u ↔ cylinder P seed s t a u' := by
  have hanswer : ∀ j, j < t → X.sameBlock a (P.request seed (P.replies seed s j)) →
      P.answer seed (P.replies seed s j) u = P.answer seed (P.replies seed s j) u' := by
    intro j hj hblock
    apply P.answer_local
    rw [← blockCells_eq hblock]
    exact he
  unfold cylinder
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  apply forall_congr'
  intro hb
  rw [hanswer j hj hb]

theorem replies_eq_iff_cylinders (P : TransferProtocol X) (seed : P.Seed)
    (s u : X.Raw) (t : ℕ) :
    P.replies seed u t = P.replies seed s t ↔
      ∀ a ∈ representatives X, cylinder P seed s t a u := by
  constructor
  · intro ht a ha j hj _
    have hj' := replies_prefix_eq P seed u s (Nat.le_of_lt hj) ht
    have hnext := replies_prefix_eq P seed u s (Nat.succ_le_of_lt hj) ht
    rw [P.replies_step, P.replies_step, hj'] at hnext
    exact List.singleton_inj.mp (List.append_cancel_left hnext)
  · intro h
    have hprefix : ∀ j, j ≤ t → P.replies seed u j = P.replies seed s j := by
      intro j
      induction j with
      | zero => intro _; rw [P.replies_zero, P.replies_zero]
      | succ j ih =>
        intro hj
        have he := ih (by omega)
        obtain ⟨a, ha, hreq⟩ := representative_exists (X := X)
          (P.request seed (P.replies seed s j))
        rw [P.replies_step, P.replies_step, he,
          h a ha j (by omega) hreq]
    exact hprefix t le_rfl

theorem cylinder_step_other (P : TransferProtocol X) (seed : P.Seed)
    (s u : X.Raw) (t : ℕ) (a : Fin (T.S.n k))
    (h : ¬ X.sameBlock a (P.request seed (P.replies seed s t))) :
    cylinder P seed s (t + 1) a u ↔ cylinder P seed s t a u := by
  constructor
  · intro hc j hj hb
    exact hc j (by omega) hb
  · intro hc j hj hb
    by_cases hjt : j < t
    · exact hc j hjt hb
    · have he : j = t := by omega
      exact False.elim (h (he ▸ hb))

theorem raw_blocks_event (hgeom : TransferGeometry X)
    (A : Fin (T.S.n k) → X.Raw → Prop)
    (hA : ∀ a ∈ representatives X, ∀ s s',
      (∀ C ∈ X.blockCells a, s C = s' C) → (A a s ↔ A a s')) :
    X.rawLaw.pr (fun s => ∀ a ∈ representatives X, A a s) =
      ∏ a ∈ representatives X, X.rawLaw.pr (A a) := by
  exact pi_pr_all_disjoint _ A (X.blockCells) (representatives X) hA
    (fun a ha b hb hne => blockCells_disjoint hgeom (representatives_not_same ha hb hne))

noncomputable def survival (X : CriticalTransferData D) (a : Fin (T.S.n k))
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) : Prop :=
  ∀ b ∈ X.criticalCoords.filter (X.sameBlock a),
    Hits (T.S.E k) PT.tiling.c x (X.criticalLabel s b) ∧
      ∀ y, z = some y → Hits (T.S.E k) PT.tiling.c y (X.criticalLabel s b)

theorem survival_local (a : Fin (T.S.n k))
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s s' : X.Raw)
    (he : ∀ C ∈ X.blockCells a, s C = s' C) :
    survival X a x z s ↔ survival X a x z s' := by
  have hlabel : ∀ b ∈ X.criticalCoords.filter (X.sameBlock a),
      X.criticalLabel s b = X.criticalLabel s' b := by
    intro b hb
    have he' := he (D.geom.cellOf (flipPos X.target b)) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    change D.fresh.label _ (s _).2 _ = D.fresh.label _ (s' _).2 _
    rw [he']
  unfold survival
  apply forall₂_congr
  intro b hb
  rw [hlabel b hb]

theorem survives_iff_blocks (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (s : X.Raw) :
    X.survives s x z ↔ ∀ a ∈ representatives X, survival X a x z s := by
  constructor
  · intro h a _ b hb
    exact h b (Finset.mem_filter.mp hb).1
  · intro h b hb
    obtain ⟨a, ha, hab⟩ := representative_exists (X := X) b
    exact h a ha b (Finset.mem_filter.mpr ⟨hb, hab⟩)

theorem raw_survival_product (hgeom : TransferGeometry X)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) :
    X.rawLaw.pr (fun s => X.survives s x z) =
      ∏ a ∈ representatives X, X.rawLaw.pr (survival X a x z) := by
  have hevent : (fun s => X.survives s x z) =
      (fun s => ∀ a ∈ representatives X, survival X a x z s) :=
    funext fun s => propext (survives_iff_blocks x z s)
  rw [hevent]
  exact raw_blocks_event hgeom _ (fun a _ => survival_local a x z)

theorem block_survival_lower (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
    (hx : X.allowed x z) :
    (0.15 : ℝ) ^ (X.criticalCoords.filter (X.sameBlock a)).card ≤
      X.rawLaw.pr (survival X a x z) :=
  Cylinder.critical_subset_survival_lower hgeom hsurv _ (Finset.filter_subset _ _) x z hx

/-- The transcript likelihood factors using only the responding blocks.
The following identity holds before any division by a block probability. -/
theorem raw_joint_product (hgeom : TransferGeometry X) (P : TransferProtocol X)
    (seed : P.Seed) (s : X.Raw) (t : ℕ) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) :
    X.rawLaw.pr (fun u => P.replies seed u t = P.replies seed s t ∧ X.survives u x z) =
      ∏ a ∈ representatives X, X.rawLaw.pr (fun u =>
        cylinder P seed s t a u ∧ survival X a x z u) := by
  have hevent : (fun u => P.replies seed u t = P.replies seed s t ∧ X.survives u x z) =
      (fun u => ∀ a ∈ representatives X, cylinder P seed s t a u ∧ survival X a x z u) := by
    funext u
    apply propext
    rw [replies_eq_iff_cylinders, survives_iff_blocks]
    exact ⟨fun h a ha => ⟨h.1 a ha, h.2 a ha⟩,
      fun h => ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩⟩
  rw [hevent]
  exact raw_blocks_event hgeom _ (fun a _ u u' he =>
    and_congr (cylinder_local P seed s t a u u' he) (survival_local a x z u u' he))

theorem raw_cylinder_product (hgeom : TransferGeometry X) (P : TransferProtocol X)
    (seed : P.Seed) (s : X.Raw) (t : ℕ) :
    X.rawLaw.pr (fun u => P.replies seed u t = P.replies seed s t) =
      ∏ a ∈ representatives X, X.rawLaw.pr (cylinder P seed s t a) := by
  have hevent : (fun u => P.replies seed u t = P.replies seed s t) =
      (fun u => ∀ a ∈ representatives X, cylinder P seed s t a u) :=
    funext fun u => propext (replies_eq_iff_cylinders P seed s u t)
  rw [hevent]
  exact raw_blocks_event hgeom _ (fun a _ => cylinder_local P seed s t a)

/-- Positive survival permits the exact conditioning formula for the tilt. -/
theorem tilted_probability (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
    (hpos : 0 < X.rawLaw.pr (fun s => X.survives s x z)) (A : X.Raw → Prop) :
    (tiltedLaw X x z).pr A =
      X.rawLaw.pr (fun s => A s ∧ X.survives s x z) /
        X.rawLaw.pr (fun s => X.survives s x z) := by
  let S := Finset.univ.filter fun s => X.survives s x z
  have hS : 0 < ∑ s ∈ S, X.rawLaw.w s := by
    simpa only [S, Finset.sum_filter, FinLaw.pr] using hpos
  unfold tiltedLaw
  rw [dif_pos hS]
  simp only [FinLaw.pr, FinLaw.cond, Finset.sum_filter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  by_cases ha : A s <;> by_cases hs : X.survives s x z <;> simp [ha, hs]

noncomputable def factor (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) (t : ℕ)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) : ℝ :=
  (X.rawLaw.pr (fun u => cylinder P seed s t a u ∧ survival X a x z u) /
    X.rawLaw.pr (cylinder P seed s t a)) / X.rawLaw.pr (survival X a x z)

theorem likelihood_product (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) (t : ℕ)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z) :
    likelihood P seed x z s t =
      ∏ a ∈ representatives X, factor P seed s t a x z := by
  have hpos : 0 < X.rawLaw.pr (fun u => X.survives u x z) := by
    have h := Cylinder.critical_subset_survival_lower hgeom hsurv X.criticalCoords
      (Finset.Subset.refl _) x z hx
    exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 0.15) _) h
  unfold likelihood
  rw [tilted_probability x z hpos, raw_joint_product hgeom,
    raw_survival_product hgeom, raw_cylinder_product hgeom]
  simp only [factor, Finset.prod_div_distrib, div_div, Finset.prod_mul_distrib]
  congr 1
  ring

private theorem pr_pos_of_atom {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A : Ω → Prop) (s : Ω) (hs : A s) (hw : 0 < Q.w s) : 0 < Q.pr A := by
  have h : Q.w s ≤ Q.pr A := by
    unfold FinLaw.pr
    calc
      _ = (if A s then Q.w s else 0) := by rw [if_pos hs]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ) (f := fun u => if A u then Q.w u else 0)
        (fun u _ => by split_ifs <;> simp [Q.nonneg])
        (Finset.mem_univ s)
  exact hw.trans_le h

private theorem pr_nonneg {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ Q.pr A := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg (fun s _ => by split_ifs <;> [exact Q.nonneg s; exact le_rfl])

private theorem pr_mono {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω)
    (A B : Ω → Prop) (h : ∀ s, A s → B s) : Q.pr A ≤ Q.pr B := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro s _
  by_cases ha : A s
  · simp [ha, h s ha]
  · simp only [ha, ↓reduceIte]
    split_ifs <;> [exact Q.nonneg s; exact le_rfl]

theorem factor_nonneg (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) (t : ℕ)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) :
    0 ≤ factor P seed s t a x z := by
  unfold factor
  exact div_nonneg (div_nonneg (pr_nonneg _ _) (pr_nonneg _ _)) (pr_nonneg _ _)

theorem factor_pos_of_likelihood (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) (t : ℕ)
    (a : Fin (T.S.n k)) (ha : a ∈ representatives X)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z)
    (hpos : 0 < likelihood P seed x z s t) : 0 < factor P seed s t a x z := by
  rw [likelihood_product hgeom hsurv P seed s t x z hx] at hpos
  by_contra hn
  have he : factor P seed s t a x z = 0 :=
    le_antisymm (le_of_not_gt hn) (factor_nonneg P seed s t a x z)
  have hz := Finset.prod_eq_zero (f := fun b => factor P seed s t b x z) ha he
  linarith

theorem factor_crude_bound (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) (t : ℕ)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k)))
    (hx : X.allowed x z) (hw : 0 < X.rawLaw.w s) :
    factor P seed s t a x z ≤
      1 / (0.15 : ℝ) ^ (X.criticalCoords.filter (X.sameBlock a)).card := by
  have hC : 0 < X.rawLaw.pr (cylinder P seed s t a) :=
    pr_pos_of_atom _ _ s (fun _ _ _ => rfl) hw
  have hlow := block_survival_lower hgeom hsurv a x z hx
  have hS : 0 < X.rawLaw.pr (survival X a x z) :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 0.15) _) hlow
  have hcap : X.rawLaw.pr (fun u => cylinder P seed s t a u ∧ survival X a x z u) /
      X.rawLaw.pr (cylinder P seed s t a) ≤ 1 := by
    apply (div_le_one hC).mpr
    exact pr_mono _ _ _ (fun _ h => h.1)
  unfold factor
  calc
    _ ≤ 1 / X.rawLaw.pr (survival X a x z) := div_le_div_of_nonneg_right hcap hS.le
    _ ≤ _ := one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 0.15) _) hlow

/-- At a single update the likelihood ratio equals the ratio of the one
responding block's factors. This uses the actual adaptive recurrence. -/
theorem likelihood_update_ratio (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw) (t : ℕ)
    (a : Fin (T.S.n k)) (ha : a ∈ representatives X)
    (hreq : X.sameBlock a (P.request seed (P.replies seed s t)))
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z)
    (hpos : 0 < likelihood P seed x z s t) :
    likelihood P seed x z s (t + 1) / likelihood P seed x z s t =
      factor P seed s (t + 1) a x z / factor P seed s t a x z := by
  have hother : ∀ b ∈ (representatives X).erase a,
      factor P seed s (t + 1) b x z = factor P seed s t b x z := by
    intro b hb
    obtain ⟨hne, hb⟩ := Finset.mem_erase.mp hb
    have hnot : ¬ X.sameBlock b (P.request seed (P.replies seed s t)) := by
      intro h
      exact representatives_not_same hb ha hne (Lane_q_s18_n2.sameBlock_trans h
        (Lane_q_s18_n2.sameBlock_symm hreq))
    have hC : cylinder P seed s (t + 1) b = cylinder P seed s t b :=
      funext fun u => propext (cylinder_step_other P seed s u t b hnot)
    simp only [factor, hC]
  have hprod : (∏ b ∈ (representatives X).erase a, factor P seed s (t + 1) b x z) =
      ∏ b ∈ (representatives X).erase a, factor P seed s t b x z :=
    Finset.prod_congr rfl hother
  have hlocalpos := factor_pos_of_likelihood hgeom hsurv P seed s t a ha x z hx hpos
  have hR (j : ℕ) : likelihood P seed x z s j =
      factor P seed s j a x z * ∏ b ∈ (representatives X).erase a, factor P seed s j b x z := by
    rw [likelihood_product hgeom hsurv P seed s j x z hx,
      ← Finset.mul_prod_erase _ _ ha]
  have hrest : (∏ b ∈ (representatives X).erase a, factor P seed s t b x z) ≠ 0 := by
    intro hzero
    rw [hR, hzero, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  rw [hR, hR, hprod]
  field_simp

theorem factor_zero (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (a : Fin (T.S.n k)) (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z) :
    factor P seed s 0 a x z = 1 := by
  have hS : 0 < X.rawLaw.pr (survival X a x z) :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 0.15) _)
      (block_survival_lower hgeom hsurv a x z hx)
  unfold FinLaw.pr at hS
  simp [factor, cylinder, FinLaw.pr, X.rawLaw.sum_one, ne_of_gt hS]

noncomputable def calls (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (a : Fin (T.S.n k)) (t : ℕ) : ℕ :=
  ((Finset.range t).filter fun j => X.sameBlock a (P.request seed (P.replies seed s j))).card

theorem calls_succ (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (a : Fin (T.S.n k)) (t : ℕ) :
    calls P seed s a (t + 1) = calls P seed s a t +
      if X.sameBlock a (P.request seed (P.replies seed s t)) then 1 else 0 := by
  unfold calls
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

theorem calls_le (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (a : Fin (T.S.n k)) (t : ℕ) (ht : t ≤ P.steps) :
    calls P seed s a t ≤ ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := by
  apply le_trans _ (P.calls_bound seed s a)
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono ht))

/-- The call bound, rather than the total number of observations, controls
the accumulated drift of a previously good local factor. -/
theorem factor_lower_before_stop (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (a : Fin (T.S.n k)) (ha : a ∈ representatives X)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z)
    (c δ : ℝ) (hδdef : δ = κ.KB *
      (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∀ t, t < stoppingTime P seed x z s c →
      1 - (calls P seed s a t : ℝ) * δ ≤ factor P seed s t a x z := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [factor_zero hgeom hsurv P seed s a x z hx]
    simp [calls]
  | succ t ih =>
    intro ht
    have hbefore : t < stoppingTime P seed x z s c := by omega
    have hlo := ih hbefore
    by_cases hreq : X.sameBlock a (P.request seed (P.replies seed s t))
    · have hpos := likelihood_positive_before_stop P seed x z c (by rw [← hδdef]; exact hδ1)
        s t hbefore
      have hlocalpos := factor_pos_of_likelihood hgeom hsurv P seed s t a ha x z hx hpos
      have hratio := likelihood_update_ratio hgeom hsurv P seed s t a ha hreq x z hx hpos
      have hn := no_stop_trigger_before P seed x z s c ht
      have hclose : |likelihood P seed x z s (t + 1) / likelihood P seed x z s t - 1| ≤ δ := by
        apply le_of_not_gt
        intro h
        exact hn (Or.inl ⟨by omega, by simpa only [Nat.add_sub_cancel, ← hδdef] using h⟩)
      have hratioLower := (abs_le.mp hclose).1
      rw [hratio] at hratioLower
      have hnext : (1 - δ) * factor P seed s t a x z ≤ factor P seed s (t + 1) a x z := by
        have h := (le_div_iff₀ hlocalpos).mp (show 1 - δ ≤
          factor P seed s (t + 1) a x z / factor P seed s t a x z by linarith)
        exact h
      have hmul := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ 1 - δ)
      have hcount : 0 ≤ (calls P seed s a t : ℝ) := Nat.cast_nonneg _
      rw [calls_succ, if_pos hreq, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg hcount (sq_nonneg δ)]
    · have hevent : cylinder P seed s (t + 1) a = cylinder P seed s t a :=
        funext fun u => propext (cylinder_step_other P seed s u t a hreq)
      rw [calls_succ, if_neg hreq, add_zero]
      simpa only [factor, hevent] using hlo

/-- The next multiplier has the paper's crude bound 2*.15^(-m). The
previous factor is bounded using the number of calls to this block. -/
theorem multiplier_crude_bound (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z)
    (c δ : ℝ) (hδdef : δ = κ.KB *
      (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hcall : (⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ : ℝ) * δ ≤ 1 / 2)
    (t : ℕ) (ht : t + 1 ≤ stoppingTime P seed x z s c) (hw : 0 < X.rawLaw.w s) :
    likelihood P seed x z s (t + 1) / likelihood P seed x z s t ≤
      2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) := by
  obtain ⟨a, ha, hreq⟩ := representative_exists (X := X) (P.request seed (P.replies seed s t))
  have hbefore : t < stoppingTime P seed x z s c := by omega
  have hpos := likelihood_positive_before_stop P seed x z c (by rw [← hδdef]; exact hδ1) s t hbefore
  rw [likelihood_update_ratio hgeom hsurv P seed s t a ha hreq x z hx hpos]
  have hcount := calls_le P seed s a t (by
    have hs := Lane_q_s18_n3.stoppingTime_le_steps P seed x z s c; omega)
  have hcountR : (calls P seed s a t : ℝ) ≤ ⌈Real.log (T.S.n k : ℝ) ^ 20⌉₊ := by
    exact_mod_cast hcount
  have hlo := factor_lower_before_stop hgeom hsurv P seed s a ha x z hx c δ hδdef hδ0 hδ1 t hbefore
  have hmul := mul_le_mul_of_nonneg_right hcountR hδ0
  have hhalf : (1 / 2 : ℝ) ≤ factor P seed s t a x z := by linarith
  have hcap := factor_crude_bound hgeom hsurv P seed s (t + 1) a x z hx hw
  have hpow : (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) ≤
      (0.15 : ℝ) ^ (X.criticalCoords.filter (X.sameBlock a)).card := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hgeom.block_size a)
  have hcap' : factor P seed s (t + 1) a x z ≤
      1 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) :=
    hcap.trans (one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 0.15) _) hpow)
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf)).mpr
  have h := mul_le_mul_of_nonneg_left hhalf (show 0 ≤
    2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) by positivity)
  have htwo : (2 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r)) *
      (1 / 2) = 1 / (0.15 : ℝ) ^ (max 1 (PT.tiling.P (D.geom.patchOf X.target)).h * D.geom.r) := by ring
  rw [htwo] at h
  exact hcap'.trans h

/-- Comparing conditioned and raw survival to the same baseline controls
the block factor, with explicit relative errors. -/
theorem survival_ratio_close (q c v η : ℝ) (hv : 0 < v) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 2) (hq : |q / v - 1| ≤ η) (hc : |c / v - 1| ≤ η) :
    |q / c - 1| ≤ 4 * η := by
  have hcBounds := abs_le.mp hc
  have hqBounds := abs_le.mp hq
  have hcRatio : 1 / 2 ≤ c / v := by linarith
  have hcPos : 0 < c := (div_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hcRatio)).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hv.le h.2))
  have hdiff : |q / v - c / v| ≤ 2 * η := by
    calc
      _ = |(q / v - 1) - (c / v - 1)| := by congr 1; ring
      _ ≤ |q / v - 1| + |c / v - 1| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (q / v - 1) (-(c / v - 1))
      _ ≤ _ := by linarith
  have hid : q / c - 1 = (q / v - c / v) / (c / v) := by field_simp <;> ring
  rw [hid, abs_div, abs_of_pos (div_pos hcPos hv)]
  apply (div_le_iff₀ (div_pos hcPos hv)).mpr
  have hmul := mul_le_mul_of_nonneg_left hcRatio (show 0 ≤ 4 * η by positivity)
  linarith

/-- Two adjacent good local factors control the observed multiplier. -/
theorem adjacent_ratio_close (r r' η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (hr : |r - 1| ≤ η) (hr' : |r' - 1| ≤ η) :
    |r' / r - 1| ≤ 4 * η := by
  have h := survival_ratio_close r' r 1 η (by norm_num) hη0 hη1
    (by simpa using hr') (by simpa using hr)
  simpa using h

/-- A multiplier exception is covered by failed local factors at its two
adjacent prefixes. This remains valid after an earlier stop. -/
theorem factor_exception_cover (hgeom : TransferGeometry X) (hsurv : SurvivalFacts X)
    (P : TransferProtocol X) (seed : P.Seed) (s : X.Raw)
    (x : Fin (T.S.N k)) (z : Option (Fin (T.S.N k))) (hx : X.allowed x z)
    (δ : ℝ) (hδdef : δ = κ.KB *
      (((max 1 (PT.tiling.P (D.geom.patchOf X.target)).h : ℕ) : ℝ) * (D.geom.r : ℝ)) * bstar T k)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (t : ℕ)
    (hbad : factorException P seed x z s (t + 1)) :
    ∃ a ∈ representatives X,
      δ / 4 < |factor P seed s t a x z - 1| ∨
      δ / 4 < |factor P seed s (t + 1) a x z - 1| := by
  by_contra hn
  have hgood : ∀ a ∈ representatives X,
      |factor P seed s t a x z - 1| ≤ δ / 4 ∧
      |factor P seed s (t + 1) a x z - 1| ≤ δ / 4 := by
    intro a ha
    constructor <;> apply le_of_not_gt
    · intro h; exact hn ⟨a, ha, Or.inl h⟩
    · intro h; exact hn ⟨a, ha, Or.inr h⟩
  have hpos : 0 < likelihood P seed x z s t := by
    rw [likelihood_product hgeom hsurv P seed s t x z hx]
    apply Finset.prod_pos
    intro a ha
    have h := (abs_le.mp (hgood a ha).1).1
    linarith
  obtain ⟨a, ha, hreq⟩ := representative_exists (X := X) (P.request seed (P.replies seed s t))
  have hratio := likelihood_update_ratio hgeom hsurv P seed s t a ha hreq x z hx hpos
  have hclose := adjacent_ratio_close _ _ (δ / 4) (by positivity) (by linarith)
    (hgood a ha).1 (hgood a ha).2
  rw [← hratio] at hclose
  have hbad' : δ < |likelihood P seed x z s (t + 1) / likelihood P seed x z s t - 1| := by
    simpa only [factorException, Nat.add_sub_cancel, ← hδdef,
      show t + 1 > 0 by omega, true_and] using hbad
  linarith

end HypercubeRamsey.S18.Lane_sol_s18_2lm.Blocks
