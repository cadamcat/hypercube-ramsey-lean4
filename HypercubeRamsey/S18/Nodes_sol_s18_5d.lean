import HypercubeRamsey.S18.PaletteRows
import HypercubeRamsey.S18.Endpoints
import HypercubeRamsey.S18.Nodes_q_s18_n5
import HypercubeRamsey.S18.Isolates_sol_s18_n5
import HypercubeRamsey.S17.Nodes_sol_s17_pool_experiment
import HypercubeRamsey.S17.Nodes_sol_s17_compat

namespace HypercubeRamsey.S18.Lane_sol_s18_5d
open Classical Filter
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

private theorem E_mono {A : Type*} [Fintype A] (P : FinLaw A) {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : P.E f ≤ P.E g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

private theorem E_mono_support {A : Type*} [Fintype A] (P : FinLaw A) {f g : A → ℝ}
    (h : ∀ a, 0 < P.w a → f a ≤ g a) : P.E f ≤ P.E g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.w a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))) (P.nonneg a)

private theorem E_nonneg {A : Type*} [Fintype A] (P : FinLaw A) {f : A → ℝ}
    (h : ∀ a, 0 ≤ f a) : 0 ≤ P.E f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (h a)

private theorem E_const {A : Type*} [Fintype A] (P : FinLaw A) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

private theorem E_mul {A : Type*} [Fintype A] (P : FinLaw A) (c : ℝ) (f : A → ℝ) :
    P.E (fun a => c * f a) = c * P.E f := by
  simp only [FinLaw.E, Finset.mul_sum]; congr 1; funext a; ring

private theorem E_sum {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (f : B → A → ℝ) :
    (∑ b, P.E (f b)) = P.E (fun a => ∑ b, f b a) := by
  simp only [FinLaw.E, Finset.mul_sum]; rw [Finset.sum_comm]

private theorem pi_E_prod_inj {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (P : ∀ c, FinLaw (Ω c)) (e : I → C) (he : Function.Injective e)
    (f : ∀ i, Ω (e i) → ℝ) :
    (FinLaw.pi P).E (fun s => ∏ i, f i (s (e i))) =
      ∏ i, (P (e i)).E (f i) := by
  have hh := Lane_sol_s17_pool.pi_E_injective_readouts P e he (fun _ x => x)
    (fun ω => ∏ i, f i (ω i))
  calc
    _ = (FinLaw.pi fun i => FinLaw.map (P (e i)) (fun x => x)).E (fun ω => ∏ i, f i (ω i)) := hh
    _ = ∏ i, (FinLaw.map (P (e i)) (fun x => x)).E (f i) := Lane_q_s17_pool.pi_expect_prod _ _
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact S16.Lane_q_s16_comp2.map_expect _ _ _

private noncomputable def poolLaw (D : LateData hPT) (C : D.geom.Cell) :
    FinLaw (D.fresh.Pool C) :=
  FinLaw.uniform Finset.univ ⟨D.l16_valid.pools_nonempty.choose C, Finset.mem_univ _⟩

private theorem iid_pi (D : LateData hPT) : D.encoding.iidLaw = FinLaw.pi (poolLaw D) := by
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro pools
  simp only [LateEncoding.iidLaw, iidPoolLaw, poolLaw, FinLaw.uniform, FinLaw.pi,
    Finset.mem_univ, ite_true, Finset.card_univ]
  rw [Fintype.card_pi]
  push_cast
  rw [Finset.prod_div_distrib]
  simp

private theorem cellPool_eq (D : LateData hPT) (C : D.geom.Cell) :
    D.cellPoolLaw C = poolLaw D C := by
  rw [LateData.cellPoolLaw, iid_pi]
  convert Lane_sol_s17_compat.pi_map_coordinate (poolLaw D) C using 1
  apply S16.Lane_q_s16_comp2.finLaw_ext
  intro P
  unfold FinLaw.map
  apply Finset.sum_congr rfl
  intro pools _
  by_cases h : pools C = P <;> simp [h]

private noncomputable def cellIntegral (D : LateData hPT) (C : D.geom.Cell)
    (f : D.fresh.State C → ℝ) : ℝ :=
  (poolLaw D C).E fun P => if D.fresh.typical C P then (D.fresh.fresh C P).E f else 0

private theorem cellIntegral_nonneg (D : LateData hPT) (C : D.geom.Cell)
    (f : D.fresh.State C → ℝ) (hf : ∀ s, 0 ≤ f s) : 0 ≤ cellIntegral D C f := by
  apply E_nonneg
  intro P
  split_ifs
  · exact E_nonneg _ hf
  · exact le_rfl

private abbrev External (D : LateData hPT) (v : Pos T k) :=
  {a : Fin (T.S.n k) // a ∈ D.externalEarly v}

private def starCell (D : LateData hPT) (v : Pos T k) : Option (External D v) → D.geom.Cell
  | none => D.geom.cellOf v
  | some a => D.geom.cellOf (flipPos v a.1)

private theorem starCell_inj (D : LateData hPT)
    (hn : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3) (v : Pos T k) :
    Function.Injective (starCell D v) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some a => exact False.elim (Lane_sol_s18_n5.external_cell_ne_own D hn v a.1 a.2 hij.symm)
  | some a =>
    cases j with
    | none => exact False.elim (Lane_sol_s18_n5.external_cell_ne_own D hn v a.1 a.2 hij)
    | some b =>
      congr 1
      exact Subtype.ext (Lane_sol_s18_n5.external_cells_injective D hn v a.2 b.2 hij)

private theorem direct_typical (D : LateData hPT) (v : Pos T k) (pools : ∀ C, D.fresh.Pool C) :
    (∀ C ∈ D.directCells v, D.fresh.typical C (pools C)) ↔
      ∀ i : Option (External D v), D.fresh.typical (starCell D v i) (pools (starCell D v i)) := by
  constructor
  · intro h i; cases i with
    | none => exact h _ (by simp [LateData.directCells, starCell])
    | some a => exact h _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨a.1,a.2,rfl⟩)))
  · intro h C hC
    rcases Finset.mem_union.mp hC with hC | hC
    · have heq := Finset.mem_singleton.mp hC; subst C; exact h none
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hC; exact h (some ⟨a,ha⟩)

private theorem prod_gate {I : Type*} [Fintype I] (p : I → Prop) (f : I → ℝ) :
    (if ∀ i, p i then ∏ i, f i else 0) = ∏ i, if p i then f i else 0 := by
  by_cases h : ∀ i, p i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Independent own-cell and external-cell fresh integration, with the local typicality gates. -/
private theorem star_integral (D : LateData hPT)
    (hn : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3) (v : Pos T k)
    (f : ∀ i : Option (External D v), D.fresh.State (starCell D v i) → ℝ) :
    D.encoding.iidLaw.E (fun pools =>
      if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
        (D.freshConfigLaw pools).E (fun s => ∏ i, f i (s (starCell D v i))) else 0) =
      ∏ i, cellIntegral D (starCell D v i) (f i) := by
  have hinj := starCell_inj D hn v
  have hinner (pools : ∀ C, D.fresh.Pool C) :
      (D.freshConfigLaw pools).E (fun s => ∏ i, f i (s (starCell D v i))) =
        ∏ i, (D.fresh.fresh (starCell D v i) (pools (starCell D v i))).E (f i) :=
    pi_E_prod_inj _ _ hinj f
  simp_rw [hinner, direct_typical, prod_gate]
  rw [iid_pi]
  exact pi_E_prod_inj (poolLaw D) (starCell D v) hinj
    (fun i P => if D.fresh.typical (starCell D v i) P then
      (D.fresh.fresh (starCell D v i) P).E (f i) else 0)

private noncomputable def pairTest (D : LateData hPT) (b : Pos T k)
    (x z y : Fin (T.S.N k)) : ℝ :=
  (if Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y then 1 else 0) /
    (rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf b)) *
      rowDeg (T.S.E k) PT.tiling.c z (PT.π (D.geom.patchOf b)))

private theorem pairTest_nonneg (D : LateData hPT) (b : Pos T k) (x z y : Fin (T.S.N k)) :
    0 ≤ pairTest D b x z y := by
  apply div_nonneg
  · split_ifs <;> norm_num
  · exact mul_nonneg (Lane_sol_s18_n5.rowDeg_nonneg D _ _) (Lane_sol_s18_n5.rowDeg_nonneg D _ _)

private noncomputable def ownPair (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) : ℝ :=
  cellIntegral D (D.geom.cellOf v) fun s =>
    D.fresh.prior (D.geom.cellOf v) s v x * D.fresh.prior (D.geom.cellOf v) s v z

private theorem ownPair_nonneg (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) :
    0 ≤ ownPair D v x z := by
  obtain ⟨_,_,hF⟩ := D.l16_valid.fresh_spec
  exact cellIntegral_nonneg _ _ _ (fun s => mul_nonneg (hF.prior_nonneg _ _ _ _) (hF.prior_nonneg _ _ _ _))

private theorem isolated_factor (D : LateData hPT)
    (hn : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3) (v : Pos T k) (x z : Fin (T.S.N k)) :
    isolatedWeight D v x z =
      if x ∈ D.palette v ∧ z ∈ D.palette v ∧ x ∈ PT.envelope (D.geom.patchOf v) ∧
        z ∈ PT.envelope (D.geom.patchOf v) ∧ D.nonconflict v x z then
        (D.chi (D.geom.patchOf v) : ℝ)^2 * ownPair D v x z *
          ∏ a ∈ D.externalEarly v, cellIntegral D (D.geom.cellOf (flipPos v a))
            (fun s => pairTest D (flipPos v a) x z (D.fresh.label _ s (flipPos v a)))
      else 0 := by
  let f : ∀ i : Option (External D v), D.fresh.State (starCell D v i) → ℝ := fun i =>
    match i with
    | none => fun s => D.fresh.prior _ s v x * D.fresh.prior _ s v z
    | some a => fun s => pairTest D (flipPos v a.1) x z (D.fresh.label _ s (flipPos v a.1))
  have h := star_integral D hn v f
  simp only [Fintype.prod_option] at h
  simp only [f, starCell] at h
  have hprod (s : Config D.fresh) :
      (∏ a : External D v, pairTest D (flipPos v a.1) x z
        (D.fresh.label _ (s (D.geom.cellOf (flipPos v a.1))) (flipPos v a.1))) =
      ∏ a ∈ D.externalEarly v, pairTest D (flipPos v a) x z
        (D.fresh.label _ (s (D.geom.cellOf (flipPos v a))) (flipPos v a)) :=
    (Finset.prod_subtype (F := (inferInstance : Fintype (External D v)))
      (D.externalEarly v) (fun _ => Iff.rfl)
      (fun a => pairTest D (flipPos v a) x z
        (D.fresh.label _ (s (D.geom.cellOf (flipPos v a))) (flipPos v a)))).symm
  have hprod' :
      (∏ a : External D v, cellIntegral D (D.geom.cellOf (flipPos v a.1))
        (fun s => pairTest D (flipPos v a.1) x z (D.fresh.label _ s (flipPos v a.1)))) =
      ∏ a ∈ D.externalEarly v, cellIntegral D (D.geom.cellOf (flipPos v a))
        (fun s => pairTest D (flipPos v a) x z (D.fresh.label _ s (flipPos v a))) :=
    (Finset.prod_subtype (F := (inferInstance : Fintype (External D v)))
      (D.externalEarly v) (fun _ => Iff.rfl)
      (fun a => cellIntegral D (D.geom.cellOf (flipPos v a))
        (fun s => pairTest D (flipPos v a) x z (D.fresh.label _ s (flipPos v a))))).symm
  simp_rw [hprod, hprod'] at h
  unfold isolatedWeight
  split_ifs
  · calc
      _ = (D.chi (D.geom.patchOf v) : ℝ)^2 * (ownPair D v x z *
          ∏ a ∈ D.externalEarly v, cellIntegral D (D.geom.cellOf (flipPos v a))
            (fun s => pairTest D (flipPos v a) x z (D.fresh.label _ s (flipPos v a)))) := by
        congr 1
      _ = _ := by ring
  · rfl

private theorem cellIntegral_le_typical (D : LateData hPT) (hD : D.Spec)
    (C : D.geom.Cell) (f : D.fresh.State C → ℝ) (hf : ∀ s, 0 ≤ f s) :
    cellIntegral D C f ≤ (D.typicalFresh C).E (fun Ps => f Ps.2) := by
  have hpos := hD.typical_positive C
  rw [cellPool_eq] at hpos
  have hmass : (∑ P ∈ D.typicalPools C, (poolLaw D C).w P) ≤ 1 := by
    rw [← (poolLaw D C).sum_one]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun P _ _ => (poolLaw D C).nonneg P)
  unfold LateData.typicalFresh
  rw [cellPool_eq]
  simp only [dif_pos hpos, FinLaw.E, FinLaw.bind, Fintype.sum_prod_type]
  unfold cellIntegral FinLaw.E
  apply Finset.sum_le_sum
  intro P _
  by_cases ht : D.fresh.typical C P
  · have hm : P ∈ D.typicalPools C := by simp [LateData.typicalPools, ht]
    simp only [if_pos ht, FinLaw.cond, if_pos hm]
    simp only [mul_assoc]
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_right
    · exact (le_div_iff₀ hpos).mpr (mul_le_of_le_one_right ((poolLaw D C).nonneg P) hmass)
    · exact E_nonneg _ hf
  · have hm : P ∉ D.typicalPools C := by simp [LateData.typicalPools, ht]
    simp [ht, FinLaw.cond, hm]

private theorem E_readout {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (read : A → B) (f : B → ℝ) :
    P.E (fun a => f (read a)) = ∑ b, P.pr (fun a => read a = b) * f b := by
  unfold FinLaw.E FinLaw.pr
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

private theorem rowDeg_eq_deg (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) :
    rowDeg (T.S.E k) PT.tiling.c x (PT.π i) = deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
  unfold rowDeg deg hit
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : Hits (T.S.E k) PT.tiling.c x y <;> simp [h]

private theorem pairTest_average (D : LateData hPT) (b : Pos T k) (x z : Fin (T.S.N k)) :
    (∑ y, (PT.π (D.geom.patchOf b)).w y * pairTest D b x z y) =
      externalPairFactor (PT := PT) (D.geom.patchOf b) x z := by
  unfold pairTest externalPairFactor
  simp only [rowDeg_eq_deg, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : Hits (T.S.E k) PT.tiling.c x y <;>
    by_cases hz : Hits (T.S.E k) PT.tiling.c z y <;>
      simp [hit, hx, hz]

private theorem pairFactor_nonneg (D : LateData hPT) (b : Pos T k) (x z : Fin (T.S.N k)) :
    0 ≤ externalPairFactor (PT := PT) (D.geom.patchOf b) x z := by
  rw [← pairTest_average D b x z]
  exact Finset.sum_nonneg fun y _ => mul_nonneg ((PT.π _).nonneg y) (pairTest_nonneg D b x z y)

private theorem cell_pair_bound (D : LateData hPT) (hD : D.Spec) (b : Pos T k)
    (hb : ¬ IsEvenRole b) (hearly : D.geom.classOf b = none) (x z : Fin (T.S.N k)) :
    cellIntegral D (D.geom.cellOf b) (fun s => pairTest D b x z (D.fresh.label _ s b)) ≤
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) *
        externalPairFactor (PT := PT) (D.geom.patchOf b) x z := by
  refine (cellIntegral_le_typical D hD _ _ (fun s => pairTest_nonneg D b x z _)).trans ?_
  rw [E_readout (D.typicalFresh (D.geom.cellOf b)) (fun Ps => D.fresh.label (D.geom.cellOf b) Ps.2 b) (pairTest D b x z), ← pairTest_average D b x z, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hD.fresh_singleton b hb hearly y)
    (pairTest_nonneg D b x z y)

/-- Any supported readout of a typical own pool extends to a globally
supported typical configuration, so it receives the retained internal certificate. -/
private theorem supported_own_valid (D : LateData hPT) (hD : D.Spec) (v : Pos T k)
    (hv : IsEvenRole v) (P : D.fresh.Pool (D.geom.cellOf v))
    (hP : D.fresh.typical (D.geom.cellOf v) P) (s : D.fresh.State (D.geom.cellOf v))
    (hs : 0 < (D.fresh.fresh (D.geom.cellOf v) P).w s) :
    ∃ cfg : Config D.fresh, cfg (D.geom.cellOf v) = s ∧ D.internalValid v cfg := by
  have hpool (C : D.geom.Cell) : ∃ P : D.fresh.Pool C, D.fresh.typical C P := by
    obtain ⟨P,hmem,_⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun P _ => (D.cellPoolLaw C).nonneg P)).mp (hD.typical_positive C)
    exact ⟨P, (Finset.mem_filter.mp hmem).2⟩
  choose baseP hbaseP using hpool
  have hstate (C : D.geom.Cell) : ∃ t, 0 < (D.fresh.fresh C (baseP C)).w t := by
    have hsum : 0 < ∑ t, (D.fresh.fresh C (baseP C)).w t := by rw [FinLaw.sum_one]; norm_num
    obtain ⟨t,_,ht⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun t _ => (D.fresh.fresh C (baseP C)).nonneg t)).mp hsum
    exact ⟨t,ht⟩
  choose baseS hbaseS using hstate
  let pools := Function.update baseP (D.geom.cellOf v) P
  let cfg := Function.update baseS (D.geom.cellOf v) s
  have htyp : ∀ C, D.fresh.typical C (pools C) := by
    intro C
    by_cases hC : C = D.geom.cellOf v
    · subst C; simpa [pools] using hP
    · simpa [pools, Function.update_of_ne hC] using hbaseP C
  have hsupport : 0 < (FinLaw.pi fun C => D.fresh.fresh C (pools C)).w cfg := by
    apply Finset.prod_pos
    intro C _
    by_cases hC : C = D.geom.cellOf v
    · subst C; simpa [pools, cfg] using hs
    · simpa [pools, cfg, Function.update_of_ne hC] using hbaseS C
  exact ⟨cfg, by simp [cfg], hD.fresh_internal pools cfg htyp hsupport v hv⟩

private noncomputable def ownMean (D : LateData hPT) (v : Pos T k) (x : Fin (T.S.N k)) : ℝ :=
  cellIntegral D (D.geom.cellOf v) (fun s => D.fresh.prior _ s v x)

private theorem ownMean_bound (D : LateData hPT) (hD : D.Spec) (v : Pos T k)
    (hv : IsEvenRole v) (x : Fin (T.S.N k)) :
    ownMean D v x ≤ κ.KB / ((PT.tiling.P (D.geom.patchOf v)).M : ℝ) := by
  have h := hD.calibration.1 v x hv
  rw [iid_pi] at h
  rw [Lane_sol_s17_compat.pi_E_coordinate (poolLaw D) (D.geom.cellOf v)
    (fun P => if D.fresh.typical (D.geom.cellOf v) P then
      (D.fresh.fresh (D.geom.cellOf v) P).E (fun s => D.fresh.prior _ s v x) else 0)] at h
  exact h

private theorem palette_own_row (D : LateData hPT) (hD : D.Spec) (Krow : ℝ)
    (hRows : PaletteRowInput D Krow) (v : Pos T k) (hv : IsEvenRole v)
    (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope (D.geom.patchOf v)) :
    (∑ z ∈ D.palette v, if D.nonconflict v x z then ownPair D v x z *
      ∏ a ∈ D.externalEarly v, externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z else 0) ≤
      (Krow / (D.chi (D.geom.patchOf v) : ℝ)) * ownMean D v x := by
  obtain ⟨_,_,hF⟩ := D.l16_valid.fresh_spec
  unfold ownPair ownMean cellIntegral
  have hswap : (∑ z ∈ D.palette v, if D.nonconflict v x z then
      (poolLaw D (D.geom.cellOf v)).E (fun P => if D.fresh.typical (D.geom.cellOf v) P then
        (D.fresh.fresh (D.geom.cellOf v) P).E (fun s =>
          D.fresh.prior _ s v x * D.fresh.prior _ s v z) else 0) *
          ∏ a ∈ D.externalEarly v, externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z else 0) =
      (poolLaw D (D.geom.cellOf v)).E (fun P => if D.fresh.typical (D.geom.cellOf v) P then
        (D.fresh.fresh (D.geom.cellOf v) P).E (fun s => D.fresh.prior _ s v x *
          ∑ z ∈ D.palette v, if D.nonconflict v x z then D.fresh.prior _ s v z *
            ∏ a ∈ D.externalEarly v, externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z else 0) else 0) := by
    unfold FinLaw.E
    simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro P _
    by_cases ht : D.fresh.typical (D.geom.cellOf v) P
    · simp only [if_pos ht, mul_ite]
      rw [Finset.sum_comm, Finset.sum_filter]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hnc : D.nonconflict v x z
      · simp only [if_pos hnc]
        apply Finset.sum_congr rfl
        intro s _
        ring
      · simp [hnc]
    · simp [ht]
  rw [hswap, ← E_mul]
  apply E_mono
  intro P
  by_cases ht : D.fresh.typical (D.geom.cellOf v) P
  · simp only [if_pos ht]
    rw [← E_mul]
    apply E_mono_support
    intro s hs
    obtain ⟨cfg,hcfg,hvalid⟩ := supported_own_valid D hD v hv P ht s hs
    have hr := hRows v hv cfg hvalid P ht (by simpa [hcfg] using hs) x hx
    simp only [LateData.sigma, hcfg] at hr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr (hF.prior_nonneg _ _ _ _)
  · simp [ht]

private theorem KB_nonneg (hκ : κ.Admissible) : 0 ≤ κ.KB :=
  le_trans (by positivity) hκ.KB_big

private noncomputable def rowTerm (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) : ℝ :=
  if z ∈ D.palette v ∧ D.nonconflict v x z then ownPair D v x z *
    ∏ a ∈ D.externalEarly v, externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z else 0

private theorem rowTerm_nonneg (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) :
    0 ≤ rowTerm D v x z := by
  unfold rowTerm
  split_ifs
  · exact mul_nonneg (ownPair_nonneg D v x z)
      (Finset.prod_nonneg fun a _ => pairFactor_nonneg D _ x z)
  · exact le_rfl

private theorem isolated_majorant (hκ : κ.Admissible) (D : LateData hPT) (hD : D.Spec)
    (hn : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3) (v : Pos T k) (hv : IsEvenRole v)
    (x z : Fin (T.S.N k)) :
    isolatedWeight D v x z ≤ (D.chi (D.geom.patchOf v) : ℝ)^2 *
      (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ (D.externalEarly v).card * rowTerm D v x z := by
  have hε : 0 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) :=
    add_nonneg (by norm_num) (mul_nonneg (KB_nonneg hκ) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rw [isolated_factor D hn]
  split_ifs with hg
  · have hprod := Finset.prod_le_prod₀
      (fun a (_ : a ∈ D.externalEarly v) => cellIntegral_nonneg D _ _ (fun s => pairTest_nonneg D _ x z _))
      (fun a (ha : a ∈ D.externalEarly v) => cell_pair_bound D hD (flipPos v a)
        (by rw [S15.evenRole_flipPos]; exact not_not.mpr hv) (Finset.mem_filter.mp ha).2.2 x z)
    rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
    have hh := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (sq_nonneg (D.chi (D.geom.patchOf v) : ℝ)) (ownPair_nonneg D v x z))
    simpa only [rowTerm, if_pos (show z ∈ D.palette v ∧ D.nonconflict v x z from ⟨hg.2.1,hg.2.2.2.2⟩),
      mul_assoc, mul_comm, mul_left_comm] using hh
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hε _)) (rowTerm_nonneg D v x z)

private theorem singleton_loss (hκ : κ.Admissible) (D : LateData hPT)
    (hn : 1 ≤ T.S.n k) (v : Pos T k) :
    (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ (D.externalEarly v).card ≤ Real.exp κ.KB := by
  have hnR : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < T.S.n k := by linarith
  have hε : 0 ≤ κ.KB * Real.rpow (T.S.n k : ℝ) (-3) :=
    mul_nonneg (KB_nonneg hκ) (Real.rpow_nonneg hnpos.le _)
  have hcount : ((D.externalEarly v).card : ℝ) ≤ T.S.n k := by exact_mod_cast (show (D.externalEarly v).card ≤ T.S.n k by simpa using Finset.card_le_univ (D.externalEarly v))
  have hp : Real.rpow (T.S.n k : ℝ) (-3) * (T.S.n k : ℝ) ≤ 1 := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hnpos.le]
    norm_num
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (pow_pos hnpos 3)).mpr
    have hh : (T.S.n k : ℝ) ≤ (T.S.n k : ℝ)^3 := by
      calc
        (T.S.n k : ℝ) = (T.S.n k : ℝ)^1 := by simp
        _ ≤ _ := pow_le_pow_right₀ hnR (by norm_num : (1 : ℕ) ≤ 3)
    simpa using hh
  calc
    (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ (D.externalEarly v).card ≤
        (Real.exp (κ.KB * Real.rpow (T.S.n k : ℝ) (-3))) ^ (D.externalEarly v).card :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (κ.KB * Real.rpow (T.S.n k : ℝ) (-3))]) _
    _ = Real.exp ((D.externalEarly v).card * (κ.KB * Real.rpow (T.S.n k : ℝ) (-3))) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp κ.KB := by
      apply Real.exp_le_exp.mpr
      calc
        (D.externalEarly v).card * (κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ≤
            (T.S.n k : ℝ) * (κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) := mul_le_mul_of_nonneg_right hcount hε
        _ ≤ κ.KB := by nlinarith [mul_le_mul_of_nonneg_left hp (KB_nonneg hκ)]

private theorem patch_mass_pos {hPT : PT.Valid} (i : Fin PT.tiling.m) : (0 : ℝ) < (PT.tiling.P i).M := by
  exact_mod_cast ((Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1).trans_eq (PT.tiling.P i).cardX)

/-- The row bound uses equation (24) on each supported own prior, then its mean bound. -/
theorem isolated_row_bound (hκ : κ.Admissible) (D : LateData hPT) (hD : D.Spec)
    (Krow : ℝ) (hKrow : 0 < Krow) (hRows : PaletteRowInput D Krow)
    (hn : 1 ≤ T.S.n k) (hlog : (2 : ℝ) ≤ Real.log (T.S.n k) ^ 3)
    (v : Pos T k) (hv : IsEvenRole v) (x : Fin (T.S.N k)) :
    (∑ z, isolatedWeight D v x z) ≤
      (Real.exp κ.KB * κ.KB * Krow) / D.paletteScale (D.rolePalette v) := by
  have hM := patch_mass_pos (hPT := hPT) (D.geom.patchOf v)
  have hchi : (0 : ℝ) < D.chi (D.geom.patchOf v) := by exact_mod_cast D.chi_pos _
  by_cases hx : x ∈ PT.envelope (D.geom.patchOf v)
  · have hs : (∑ z, rowTerm D v x z) ≤ (Krow / (D.chi (D.geom.patchOf v) : ℝ)) * ownMean D v x := by
      have hh := palette_own_row D hD Krow hRows v hv x hx
      simpa [rowTerm, ite_and, Finset.sum_ite_mem] using hh
    have hε : 0 ≤ 1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3) :=
      add_nonneg (by norm_num) (mul_nonneg (KB_nonneg hκ) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have hmean0 : 0 ≤ ownMean D v x := by
      obtain ⟨_,_,hF⟩ := D.l16_valid.fresh_spec
      exact cellIntegral_nonneg D _ _ (fun s => hF.prior_nonneg _ _ _ _)
    have hs0 : 0 ≤ ∑ z, rowTerm D v x z := Finset.sum_nonneg fun z _ => rowTerm_nonneg D v x z
    calc
      (∑ z, isolatedWeight D v x z) ≤
          (D.chi (D.geom.patchOf v) : ℝ)^2 *
          (1 + κ.KB * Real.rpow (T.S.n k : ℝ) (-3)) ^ (D.externalEarly v).card * ∑ z, rowTerm D v x z := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun z _ => isolated_majorant hκ D hD hlog v hv x z
      _ ≤ (D.chi (D.geom.patchOf v) : ℝ)^2 * Real.exp κ.KB *
          ((Krow / (D.chi (D.geom.patchOf v) : ℝ)) * (κ.KB / (PT.tiling.P (D.geom.patchOf v)).M)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (singleton_loss hκ D hn v) (sq_nonneg _)
        · exact hs.trans (mul_le_mul_of_nonneg_left (ownMean_bound D hD v hv x) (div_nonneg hKrow.le hchi.le))
        · exact hs0
        · positivity
      _ = _ := by
        unfold LateData.paletteScale LateData.rolePalette
        dsimp
        field_simp [hM.ne', hchi.ne']
        <;> ring
  · have hz : ∀ z, isolatedWeight D v x z = 0 := by
      intro z; simp [isolatedWeight, hx]
    simp only [hz, Finset.sum_const_zero]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (KB_nonneg hκ)) hKrow.le
    · exact div_nonneg hM.le hchi.le

private theorem height_log (D : LateData hPT) (hlog : (1 : ℝ) ≤ Real.log (T.S.n k))
    (i : Fin PT.tiling.m) : ((PT.tiling.P i).h : ℝ) ≤ Real.log (T.S.n k) := by
  obtain ⟨physical⟩ := D.l16_valid.physical
  exact (physical.quantitative.height_bound i).trans
    ((Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1/10 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))

private theorem prefix_log (D : LateData hPT) (hlog : (1 : ℝ) ≤ Real.log (T.S.n k))
    (i : Fin PT.tiling.m) : ((PT.tiling.P i).ℓ : ℝ) ≤ Real.log (T.S.n k) := by
  obtain ⟨physical⟩ := D.l16_valid.physical
  exact (physical.quantitative.prefix_bound i).trans (Real.sqrt_le_self_iff.mpr (Or.inr hlog))

private theorem gain_nonneg (hκ : κ.Admissible) (i : Fin PT.tiling.m) : 0 ≤ PT.tiling.gain i := by
  have ha : 0 ≤ κ.a := by rw [hκ.a_eq]; exact div_nonneg hκ.θ_rng.1.le (by norm_num)
  cases hm : PT.tiling.mode <;> simp [Tiling.gain, hm] <;> positivity

private theorem own_cap (D : LateData hPT) (hD : D.Spec)
    (hlog : (1 : ℝ) ≤ Real.log (T.S.n k)) (v : Pos T k) (hv : IsEvenRole v)
    (P : D.fresh.Pool (D.geom.cellOf v)) (hP : D.fresh.typical (D.geom.cellOf v) P)
    (s : D.fresh.State (D.geom.cellOf v)) (hs : 0 < (D.fresh.fresh (D.geom.cellOf v) P).w s)
    (x : Fin (T.S.N k)) :
    D.fresh.prior _ s v x ≤ 2 * Real.exp (Real.log (T.S.n k)) / (PT.tiling.P (D.geom.patchOf v)).M := by
  obtain ⟨cfg,hcfg,hvalid⟩ := supported_own_valid D hD v hv P hP s hs
  have hM := patch_mass_pos (hPT := hPT) (D.geom.patchOf v)
  have hσ : 0 ≤ D.fresh.prior _ s v x := by simpa [LateData.sigma, hcfg] using hvalid.1 x
  by_cases hc : PT.tiling.mode.isCluster
  · have hcap := hvalid.2.2.1
    simp only [if_pos hc] at hcap
    have hcapx := hcap x
    simp only [LateData.sigma, hcfg] at hcapx
    have hpow : (2 : ℝ) ^ (PT.tiling.P (D.geom.patchOf v)).h ≤ Real.exp (Real.log (T.S.n k)) := by
      calc
        _ ≤ Real.exp 1 ^ (PT.tiling.P (D.geom.patchOf v)).h :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
        _ = Real.exp ((PT.tiling.P (D.geom.patchOf v)).h : ℝ) := by rw [← Real.exp_nat_mul]; simp
        _ ≤ _ := Real.exp_le_exp.mpr (height_log D hlog _)
    have hexp : Real.exp (-500 * PT.tiling.gain (D.geom.patchOf v)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [gain_nonneg D.constants (D.geom.patchOf v)])
    have hMN : ((PT.tiling.P (D.geom.patchOf v)).M : ℝ) ≤ T.S.N k := by
      exact_mod_cast (show (PT.tiling.P (D.geom.patchOf v)).M ≤ T.S.N k from
        (PT.tiling.P _).cardX ▸ (by simpa using Finset.card_le_univ (PT.tiling.P (D.geom.patchOf v)).X))
    apply (le_div_iff₀ hM).mpr
    have hh := mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (PT.tiling.P (D.geom.patchOf v)).h)
    nlinarith [mul_le_mul_of_nonneg_right hMN hσ, Real.exp_pos (Real.log (T.S.n k))]
  · obtain ⟨q,hq,huniform⟩ := (show ∃ q ∈ PT.activeVertices, ∀ x, D.sigma v cfg x =
        if x ∈ PT.mesh.corner q (D.geom.patchOf v) then 1 / ((PT.mesh.corner q (D.geom.patchOf v)).card : ℝ) else 0 from
        by simpa [hc] using hvalid.2.2.1)
    have hsize := hD.corner_mass (D.geom.patchOf v) q hq
    have hsizepos : (0 : ℝ) < (PT.mesh.corner q (D.geom.patchOf v)).card := by linarith
    have hh : (1 : ℝ) / (PT.mesh.corner q (D.geom.patchOf v)).card ≤ 2 / (PT.tiling.P (D.geom.patchOf v)).M := by
      apply (div_le_div_iff₀ hsizepos hM).mpr
      simpa using hsize
    have huniformx := huniform x
    simp only [LateData.sigma, hcfg] at huniformx
    rw [huniformx]
    split_ifs
    · refine hh.trans ?_
      apply div_le_div_of_nonneg_right _ hM.le
      have he : (1 : ℝ) ≤ Real.exp (Real.log (T.S.n k)) := Real.one_le_exp_iff.mpr (by linarith)
      linarith
    · positivity

private theorem ownPair_cap (D : LateData hPT) (hD : D.Spec)
    (hlog : (1 : ℝ) ≤ Real.log (T.S.n k)) (v : Pos T k) (hv : IsEvenRole v)
    (x z : Fin (T.S.N k)) :
    ownPair D v x z ≤ (2 * Real.exp (Real.log (T.S.n k)) / (PT.tiling.P (D.geom.patchOf v)).M)^2 := by
  let c : ℝ := 2 * Real.exp (Real.log (T.S.n k)) / (PT.tiling.P (D.geom.patchOf v)).M
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨_,_,hF⟩ := D.l16_valid.fresh_spec
  unfold ownPair cellIntegral
  rw [← E_const (poolLaw D (D.geom.cellOf v)) (c^2)]
  apply E_mono
  intro P
  split_ifs with hP
  · rw [← E_const (D.fresh.fresh (D.geom.cellOf v) P) (c^2)]
    apply E_mono_support
    intro s hs
    simpa only [pow_two] using mul_le_mul (own_cap D hD hlog v hv P hP s hs x)
      (own_cap D hD hlog v hv P hP s hs z) (hF.prior_nonneg _ _ _ _) hc
  · positivity

private theorem pair_numerator_identity (i : Fin PT.tiling.m) (x z : Fin (T.S.N k)) :
    4 * (∑ y, (PT.π i).w y * hit (T.S.E k) PT.tiling.c x y * hit (T.S.E k) PT.tiling.c z y) =
      corr (T.S.E k) PT.tiling.c (PT.π i).w x z +
        2 * deg (T.S.E k) PT.tiling.c (PT.π i).w x +
        2 * deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1 := by
  rw [← (PT.π i).sum_eq_one]
  unfold corr deg fv
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

private theorem pairFactor_small (i : Fin PT.tiling.m) (x z : Fin (T.S.N k))
    (hx : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1/2| ≤ 0.00001)
    (hz : |deg (T.S.E k) PT.tiling.c (PT.π i).w z - 1/2| ≤ 0.00001)
    (hc : |corr (T.S.E k) PT.tiling.c (PT.π i).w x z| ≤ 0.00001) :
    externalPairFactor (PT := PT) i x z ≤ Real.exp 0.001 := by
  obtain ⟨hxl,hxu⟩ := abs_le.mp hx
  obtain ⟨hzl,hzu⟩ := abs_le.mp hz
  have hn := pair_numerator_identity (PT := PT) i x z
  have hcl := (abs_le.mp hc).2
  have hdx : (0 : ℝ) < deg (T.S.E k) PT.tiling.c (PT.π i).w x := by linarith
  have hdz : (0 : ℝ) < deg (T.S.E k) PT.tiling.c (PT.π i).w z := by linarith
  have hprod : (0.49999 : ℝ)^2 ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x * deg (T.S.E k) PT.tiling.c (PT.π i).w z := by
    nlinarith [mul_le_mul (show (0.49999 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w x by linarith)
      (show (0.49999 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π i).w z by linarith) (by norm_num : (0 : ℝ) ≤ 0.49999) hdx.le]
  refine le_trans ?_ (show (1.001 : ℝ) ≤ Real.exp 0.001 by linarith [Real.add_one_le_exp (0.001 : ℝ)])
  unfold externalPairFactor
  apply (div_le_iff₀ (mul_pos hdx hdz)).mpr
  nlinarith

private theorem pairFactor_cross (D : LateData hPT) (i j : Fin PT.tiling.m) (hji : j ≠ i)
    (x z : Fin (T.S.N k)) (hx : x ∈ PT.envelope i) (hz : z ∈ PT.envelope i)
    (hb : 3 * bstar T k ≤ 1/4) : externalPairFactor (PT := PT) j x z ≤ 16 := by
  have hdx := (abs_le.mp (hPT.envelope_other_degree i j hji x hx)).1
  have hdz := (abs_le.mp (hPT.envelope_other_degree i j hji z hz)).1
  have hdx' : (1/4 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π j).w x := by linarith
  have hdz' : (1/4 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π j).w z := by linarith
  have hprod := mul_le_mul hdx' hdz' (by norm_num : (0 : ℝ) ≤ 1/4) (by linarith : 0 ≤ deg (T.S.E k) PT.tiling.c (PT.π j).w x)
  have hnum : (∑ y, (PT.π j).w y * hit (T.S.E k) PT.tiling.c x y * hit (T.S.E k) PT.tiling.c z y) ≤ 1 := by
    rw [← (PT.π j).sum_eq_one]
    apply Finset.sum_le_sum
    intro y _
    by_cases hxy : Hits (T.S.E k) PT.tiling.c x y <;> by_cases hzy : Hits (T.S.E k) PT.tiling.c z y <;>
      simp [hit,hxy,hzy,(PT.π j).nonneg y]
  unfold externalPairFactor
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < deg (T.S.E k) PT.tiling.c (PT.π j).w x * deg (T.S.E k) PT.tiling.c (PT.π j).w z)).mpr
  nlinarith

private noncomputable def degreeConstant (κ : CConsts) : ℝ := |κ.Kbd| + 4000 * max 0 κ.KB + 10

private theorem degree_drift (hκ : κ.Admissible) (D : LateData hPT)
    (hlog : (1 : ℝ) ≤ Real.log (T.S.n k)) (hn : (0 : ℝ) < T.S.n k)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope i) :
    |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1/2| ≤
      degreeConstant κ * Real.log (T.S.n k) / T.S.n k := by
  have hown := hPT.envelope_degree i x hx
  have hC0 : 0 ≤ degreeConstant κ := by unfold degreeConstant; positivity
  have hCbd : κ.Kbd ≤ degreeConstant κ := by
    have hh := le_abs_self κ.Kbd
    have := le_max_left (0 : ℝ) κ.KB
    unfold degreeConstant; linarith
  have hCdir : 4000 * κ.KB ≤ degreeConstant κ := by
    have := le_max_right (0 : ℝ) κ.KB
    unfold degreeConstant; nlinarith [abs_nonneg κ.Kbd]
  have hCcl : 10 ≤ degreeConstant κ := by unfold degreeConstant; nlinarith [abs_nonneg κ.Kbd, le_max_left (0 : ℝ) κ.KB]
  cases hm : PT.tiling.mode with
  | bounded =>
    simp only [OwnDegOK, hm] at hown
    refine hown.trans (div_le_div_of_nonneg_right ?_ hn.le)
    nlinarith
  | lowDirect =>
    simp only [OwnDegOK, hm] at hown
    have hg : ((PT.tiling.P i).g : ℝ) ≤ 1000 * κ.KB * Real.log (T.S.n k) := by
      have hh := D.l16_valid.gain_upper i
      simp only [Tiling.gain,hm] at hh
      linarith
    apply abs_le.mpr
    constructor
    · have hnn : 0 ≤ ((PT.tiling.P i).g : ℝ) / (4 * T.S.n k) := by positivity
      have hb : 0 ≤ degreeConstant κ * Real.log (T.S.n k) / T.S.n k := by positivity
      linarith [hown.1]
    · apply (le_div_iff₀ hn).mpr
      have hh := (le_div_iff₀ hn).mp (show deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1/2 ≤ 4 * (PT.tiling.P i).g / T.S.n k by linarith [hown.2])
      nlinarith [mul_le_mul_of_nonneg_right hCdir (by linarith : 0 ≤ Real.log (T.S.n k))]
  | lowCluster =>
    simp only [OwnDegOK, hm] at hown
    have hh := (hPT.tiling_valid.cluster_data (Or.inl hm) i).2.2.2.2.2.2.2.1
    simp only [if_pos (show PT.tiling.mode = .lowCluster from hm)] at hh
    have hpow : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤ Real.log (T.S.n k) := by
      by_cases hq : (1 : ℝ) ≤ (PT.tiling.P i).q
      · have hexp : (κ.Cb : ℝ) ≤ κ.Mlo := by linarith [hκ.Mlo_big]
        exact ((Real.rpow_le_rpow_of_exponent_le hq hexp).trans hh).trans (height_log D hlog i)
      · have hq' : (PT.tiling.P i).q ≤ 1 := by exact_mod_cast (le_of_not_ge hq)
        have hCb : 0 ≤ κ.Cb := by
          have hpos : 0 < 100 * κ.aC / κ.aB := div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
          linarith [hκ.Cb_big]
        have hp : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤ 1 :=
          Real.rpow_le_one (Nat.cast_nonneg _) (by exact_mod_cast hq') hCb
        exact hp.trans hlog
    refine hown.trans (div_le_div_of_nonneg_right ?_ hn.le)
    nlinarith [mul_le_mul_of_nonneg_right hCcl (by linarith : 0 ≤ Real.log (T.S.n k))]
  | highDirect => exact False.elim (by simpa [hm,Mode.isLow] using D.low_mode)
  | highSmall => exact False.elim (by simpa [hm,Mode.isLow] using D.low_mode)
  | highLarge => exact False.elim (by simpa [hm,Mode.isLow] using D.low_mode)

private theorem xi_small (hκ : κ.Admissible) : κ.ξ ≤ (0.00001 : ℝ) := by
  have hexp : -(10 * (κ.u : ℝ) + 100) ≤ (-10 : ℝ) := by have := (Nat.cast_nonneg κ.u : (0 : ℝ) ≤ κ.u); linarith
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have heq : (2 : ℝ)^(-10 : ℝ) = 1/1024 := by norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [heq] at hp
  have hh := mul_le_mul_of_nonneg_left hp hκ.α_rng.1.le
  have hξ := hκ.ξ_rng.2
  simp only [Real.rpow_eq_pow] at hξ
  nlinarith [hξ, hκ.α_rng.2]

private theorem corr_colour {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Fin N → ℝ) (x z : Fin N) : corr E c π x z = corr E true π x z := by
  cases c with
  | true => rfl
  | false =>
    unfold corr
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : E x y <;> by_cases hz : E z y <;> simp [fv, hit, Hits, hx, hz] <;> ring

private theorem pair_product_bound (hκ : κ.Admissible) (D : LateData hPT)
    (hlog : (1 : ℝ) ≤ Real.log (T.S.n k)) (hdeg : degreeConstant κ * Real.log (T.S.n k) / T.S.n k ≤ 0.00001)
    (hb : 3 * bstar T k ≤ 1/4) (hn : (0 : ℝ) < T.S.n k)
    (v : Pos T k) (x z : Fin (T.S.N k))
    (hx : x ∈ PT.envelope (D.geom.patchOf v)) (hz : z ∈ PT.envelope (D.geom.patchOf v))
    (hnc : D.nonconflict v x z) :
    (∏ a ∈ D.externalEarly v, externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z) ≤
      Real.exp (0.001 * (T.S.n k : ℝ) + 16 * Real.log (T.S.n k)) := by
  let C := (D.externalEarly v).filter fun a => a.val < (PT.tiling.P (D.geom.patchOf v)).ℓ
  have hCcard : C.card ≤ (PT.tiling.P (D.geom.patchOf v)).ℓ := by
    have hinj : Set.InjOn (fun a : Fin (T.S.n k) => a.val) (C : Set _) := fun _ _ _ _ h => Fin.ext h
    have hsubset : C.image (fun a => a.val) ⊆ Finset.range (PT.tiling.P (D.geom.patchOf v)).ℓ := by
      rintro j hj
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
    calc
      C.card = (C.image (fun a => a.val)).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (PT.tiling.P (D.geom.patchOf v)).ℓ).card := Finset.card_le_card hsubset
      _ = _ := Finset.card_range _
  have hprod : (∏ a ∈ D.externalEarly v, externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z) ≤
      ∏ a ∈ D.externalEarly v, Real.exp 0.001 * (if a ∈ C then (16 : ℝ) else 1) := by
    apply Finset.prod_le_prod₀ (fun a _ => pairFactor_nonneg D _ x z)
    intro a ha
    by_cases hp : D.geom.patchOf (flipPos v a) = D.geom.patchOf v
    · have hh := pairFactor_small (D.geom.patchOf v) x z
        ((degree_drift hκ D hlog hn _ x hx).trans hdeg)
        ((degree_drift hκ D hlog hn _ z hz).trans hdeg)
        (by
          have heq : pairCorr (T.S.E k) true (PT.π (D.geom.patchOf v)) x z = corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z := by
            simpa only [pairCorr,ite_true] using (corr_colour (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z).symm
          have hh : |corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z| ≤ κ.ξ := by
            simpa only [LateData.nonconflict,heq] using hnc
          exact hh.trans (xi_small hκ))
      rw [hp]
      refine hh.trans ?_
      split_ifs <;> nlinarith [Real.exp_pos (0.001 : ℝ)]
    · have hcross : a ∈ C := by
        apply Finset.mem_filter.mpr
        refine ⟨ha, ?_⟩
        by_contra hh
        exact hp (Lane_q_s17_pool.lowGeom_patch_flip_of_after_prefix D.geom hPT v a (le_of_not_gt hh))
      rw [if_pos hcross]
      refine (pairFactor_cross D _ _ hp x z hx hz hb).trans ?_
      have h1 : (1 : ℝ) ≤ Real.exp 0.001 := Real.one_le_exp_iff.mpr (by norm_num)
      nlinarith
  have heq : (∏ a ∈ D.externalEarly v, Real.exp 0.001 * (if a ∈ C then (16 : ℝ) else 1)) =
      Real.exp (0.001 * (D.externalEarly v).card) * (16 : ℝ)^C.card := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul]
    congr 1
    · congr 1; ring
    · rw [Finset.prod_ite]
      have heq : (D.externalEarly v).filter (fun a => a ∈ C) = C := by
        ext a; simp only [Finset.mem_filter]; constructor
        · exact fun h => h.2
        · intro h; exact ⟨(Finset.mem_filter.mp h).1,h⟩
      simp [heq]
  rw [heq] at hprod
  refine hprod.trans ?_
  have hcross : (16 : ℝ)^C.card ≤ Real.exp (16 * Real.log (T.S.n k)) := by
    calc
      _ ≤ (Real.exp 16)^C.card := pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (16 : ℝ)]) _
      _ = Real.exp (16 * (C.card : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hc : (C.card : ℝ) ≤ (PT.tiling.P (D.geom.patchOf v)).ℓ := by exact_mod_cast hCcard
        linarith [prefix_log D hlog (D.geom.patchOf v)])
  rw [Real.exp_add]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    have hcount : ((D.externalEarly v).card : ℝ) ≤ T.S.n k := by exact_mod_cast (show (D.externalEarly v).card ≤ T.S.n k by simpa using Finset.card_le_univ (D.externalEarly v))
    linarith
  · exact hcross
  · positivity
  · positivity

/-- Entry estimate after independent fresh integration; all logarithmic
losses are absorbed before the eventual index. -/
theorem isolated_entry_bound (hκ : κ.Admissible) (D : LateData hPT) (hD : D.Spec)
    (hn : 1 ≤ T.S.n k) (hlog : (2 : ℝ) ≤ Real.log (T.S.n k))
    (hdeg : degreeConstant κ * Real.log (T.S.n k) / T.S.n k ≤ 0.00001)
    (hb : 3 * bstar T k ≤ 1/4)
    (hsmall : κ.KB + 4 + 18 * Real.log (T.S.n k) ≤ 0.009 * (T.S.n k : ℝ))
    (v : Pos T k) (hv : IsEvenRole v) (x z : Fin (T.S.N k)) :
    isolatedWeight D v x z ≤ (D.paletteScale (D.rolePalette v))⁻¹^2 * Real.exp (0.01 * (T.S.n k : ℝ)) := by
  have hM := patch_mass_pos (hPT := hPT) (D.geom.patchOf v)
  have hchi : (0 : ℝ) < D.chi (D.geom.patchOf v) := by exact_mod_cast D.chi_pos _
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hlog3 : (2 : ℝ) ≤ Real.log (T.S.n k)^3 := by
    have h2 : (2 : ℝ)^3 ≤ Real.log (T.S.n k)^3 := pow_le_pow_left₀ (by norm_num) (show (2 : ℝ) ≤ Real.log (T.S.n k) by simpa only [Function.comp_apply] using hlog) 3
    norm_num at h2
    linarith
  by_cases hg : x ∈ D.palette v ∧ z ∈ D.palette v ∧ x ∈ PT.envelope (D.geom.patchOf v) ∧
      z ∈ PT.envelope (D.geom.patchOf v) ∧ D.nonconflict v x z
  · have hmaj := isolated_majorant hκ D hD hlog3 v hv x z
    rw [rowTerm, if_pos ⟨hg.2.1,hg.2.2.2.2⟩] at hmaj
    have hprod := pair_product_bound hκ D (by linarith) hdeg hb hnR v x z hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2
    have hown := ownPair_cap D hD (by linarith) v hv x z
    have hupper : isolatedWeight D v x z ≤ (D.chi (D.geom.patchOf v) : ℝ)^2 * Real.exp κ.KB *
        ((2 * Real.exp (Real.log (T.S.n k)) / (PT.tiling.P (D.geom.patchOf v)).M)^2 *
          Real.exp (0.001 * (T.S.n k : ℝ) + 16 * Real.log (T.S.n k))) := by
      refine hmaj.trans (mul_le_mul ?_ ?_ ?_ ?_)
      · exact mul_le_mul_of_nonneg_left (singleton_loss hκ D hn v) (sq_nonneg _)
      · exact mul_le_mul hown hprod (Finset.prod_nonneg fun a _ => pairFactor_nonneg D _ x z) (sq_nonneg _)
      · exact mul_nonneg (ownPair_nonneg D v x z) (Finset.prod_nonneg fun a _ => pairFactor_nonneg D _ x z)
      · positivity
    have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      isolatedWeight D v x z ≤ _ := hupper
      _ = (D.paletteScale (D.rolePalette v))⁻¹^2 *
          (4 * Real.exp (κ.KB + 0.001 * (T.S.n k : ℝ) + 18 * Real.log (T.S.n k))) := by
        unfold LateData.paletteScale LateData.rolePalette
        dsimp
        simp only [Real.exp_add, show Real.exp (18 * Real.log (T.S.n k)) = (Real.exp (Real.log (T.S.n k)))^18 from by simpa using Real.exp_nat_mul (Real.log (T.S.n k)) 18, show Real.exp (16 * Real.log (T.S.n k)) = (Real.exp (Real.log (T.S.n k)))^16 from by simpa using Real.exp_nat_mul (Real.log (T.S.n k)) 16, pow_two]
        field_simp [hM.ne', hchi.ne']
        <;> ring
      _ ≤ (D.paletteScale (D.rolePalette v))⁻¹^2 *
          Real.exp (κ.KB + 4 + 0.001 * (T.S.n k : ℝ) + 18 * Real.log (T.S.n k)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        rw [show κ.KB + 4 + 0.001 * (T.S.n k : ℝ) + 18 * Real.log (T.S.n k) =
          4 + (κ.KB + 0.001 * (T.S.n k : ℝ) + 18 * Real.log (T.S.n k)) by ring, Real.exp_add (4 : ℝ) (κ.KB + 0.001 * (T.S.n k : ℝ) + 18 * Real.log (T.S.n k))]
        exact mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)
  · simp only [isolatedWeight, if_neg hg]
    positivity

/-- Uniform constants and eventual size conditions for both isolate bounds. -/
theorem isolate_facts (hκ : κ.Admissible) (T : Stage) (Krow : ℝ) (hKrow : 0 < Krow) :
    ∃ KI : ℝ, 1 ≤ KI ∧ ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : LateData hPT, D.Spec → PaletteRowInput D Krow → IsolateKernelFacts D KI := by
  let KI := max 1 (Real.exp κ.KB * κ.KB * Krow)
  refine ⟨KI, le_max_left _ _, ?_⟩
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT := Real.tendsto_log_atTop.comp hnT
  have hC : 0 ≤ degreeConstant κ := by unfold degreeConstant; positivity
  have hlogdiv : Tendsto (fun k => Real.log (T.S.n k : ℝ) / T.S.n k) atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp hnT
  have hdegT : Tendsto (fun k => degreeConstant κ * Real.log (T.S.n k : ℝ) / T.S.n k) atTop (nhds 0) := by
    simpa [mul_div_assoc] using hlogdiv.const_mul (degreeConstant κ)
  have hsmallT : Tendsto (fun k => (κ.KB + 4 + 18 * Real.log (T.S.n k : ℝ)) / T.S.n k) atTop (nhds 0) := by
    have hconstant := (tendsto_const_nhds.div_atTop hnT : Tendsto (fun k => (κ.KB + 4) / (T.S.n k : ℝ)) atTop (nhds 0))
    simpa [add_div, mul_div_assoc] using hconstant.add (hlogdiv.const_mul 18)
  have hbT : Tendsto (fun k => 3 * bstar T k) atTop (nhds 0) := by
    have hb : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
      unfold bstar
      convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hnT using 1
      ext k; congr 1; norm_num
    simpa using hb.const_mul 3
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 1, hlogT.eventually_ge_atTop 2,
    hdegT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.00001)),
    hsmallT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 0.009)),
    hbT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))] with k hn hlog hdeg hsmall hb
  intro PT hPT D hD hRows v hv x z
  have hnR : (0 : ℝ) < T.S.n k := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hlog3 : (2 : ℝ) ≤ Real.log (T.S.n k)^3 := by
    have h2 : (2 : ℝ)^3 ≤ Real.log (T.S.n k)^3 := pow_le_pow_left₀ (by norm_num) (show (2 : ℝ) ≤ Real.log (T.S.n k) by simpa only [Function.comp_apply] using hlog) 3
    norm_num at h2
    linarith
  refine ⟨Lane_q_s18_n5.isolatedWeight_nonneg D v x z, Lane_q_s18_n5.isolatedWeight_symm D v x z, ?_, ?_⟩
  · refine (isolated_row_bound hκ D hD Krow hKrow hRows hn hlog3 v hv x).trans ?_
    apply div_le_div_of_nonneg_right (le_max_right _ _) (div_nonneg (patch_mass_pos (hPT := hPT) _).le (Nat.cast_nonneg _))
  · exact isolated_entry_bound hκ D hD hn hlog hdeg.le hb.le ((div_le_iff₀ hnR).mp hsmall.le) v hv x z

end HypercubeRamsey.S18.Lane_sol_s18_5d
