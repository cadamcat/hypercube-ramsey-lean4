import HypercubeRamsey.S17.Nodes_sol_s17_pool
import HypercubeRamsey.S16.Comparisons_q_s16_comp2

namespace HypercubeRamsey.Lane_sol_s17_pool

open Classical
open scoped BigOperators
open S16.Lane_q_s16_comp2

/-- Predicates read from distinct coordinates of a product law are independent. -/
theorem pi_pr_injective_coordinates {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (P : ∀ c, FinLaw (Ω c)) (e : I → C) (he : Function.Injective e)
    (A : ∀ i, Ω (e i) → Prop) :
    (FinLaw.pi P).pr (fun s => ∀ i, A i (s (e i))) =
      ∏ i, (P (e i)).pr (A i) := by
  classical
  let B : ∀ c, Ω c → Prop := fun c s => ∀ (i : I) (h : e i = c), A i (h.symm ▸ s)
  have hB (i : I) : B (e i) = A i := by
    funext s
    apply propext
    constructor
    · intro h
      exact h i rfl
    · intro h j hj
      have hji : j = i := he hj
      subst j
      simpa using h
  have hEvent : (fun s : ∀ c, Ω c => ∀ i, A i (s (e i))) =
      (fun s => ∀ c, B c (s c)) := by
    funext s
    apply propext
    constructor
    · intro h c i hi
      subst c
      exact h i
    · intro h i
      simpa [hB i] using h (e i)
  rw [hEvent, Lane_q_s17_pool.pi_pr_forall]
  let S := Finset.univ.image e
  have hOutside : ∀ c ∉ S, (P c).pr (B c) = 1 := by
    intro c hc
    have htrue : ∀ s, B c s := by
      intro s i hi
      exact False.elim (hc (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
    simpa [FinLaw.pr, htrue] using (P c).sum_one
  calc
    (∏ c, (P c).pr (B c)) = ∏ c ∈ S, (P c).pr (B c) :=
      (Finset.prod_subset (Finset.subset_univ S) (fun c _ hc => hOutside c hc)).symm
    _ = ∏ i, (P (e i)).pr (B (e i)) := by
      dsimp [S]
      rw [Finset.prod_image (fun i _ j _ hij => he hij)]
    _ = ∏ i, (P (e i)).pr (A i) := by simp_rw [hB]

/-- Distinct coordinate readouts push a product law to their product marginal. -/
theorem pi_map_injective_readouts {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    {β : I → Type*} [∀ i, Fintype (β i)]
    (P : ∀ c, FinLaw (Ω c)) (e : I → C) (he : Function.Injective e)
    (read : ∀ i, Ω (e i) → β i) :
    FinLaw.map (FinLaw.pi P) (fun s i => read i (s (e i))) =
      FinLaw.pi (fun i => FinLaw.map (P (e i)) (read i)) := by
  classical
  apply finLaw_ext
  intro z
  rw [map_weight_eq_pr]
  have hevent : (fun s : ∀ c, Ω c => (fun i => read i (s (e i))) = z) =
      (fun s => ∀ i, read i (s (e i)) = z i) := by
    funext s
    exact propext ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [hevent, pi_pr_injective_coordinates P e he (fun i s => read i s = z i)]
  change (∏ i, (P (e i)).pr (fun s => read i s = z i)) =
    ∏ i, (FinLaw.map (P (e i)) (read i)).w (z i)
  simp_rw [map_weight_eq_pr]

/-- Expectations on distinct coordinate readouts use only their independent marginals. -/
theorem pi_E_injective_readouts {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    {β : I → Type*} [∀ i, Fintype (β i)]
    (P : ∀ c, FinLaw (Ω c)) (e : I → C) (he : Function.Injective e)
    (read : ∀ i, Ω (e i) → β i) (f : (∀ i, β i) → ℝ) :
    (FinLaw.pi P).E (fun s => f (fun i => read i (s (e i)))) =
      (FinLaw.pi fun i => FinLaw.map (P (e i)) (read i)).E f := by
  classical
  rw [← S16.Lane_q_s16_comp2.map_expect, pi_map_injective_readouts P e he read]

/-- The own cell and all external early cells form an injective coordinate selection. -/
theorem star_cells_injective {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) : Function.Injective
      (fun i : Option {w : Pos T k // w ∈ D.externalEarly v} =>
        match i with | none => D.G.cellOf v | some w => D.G.cellOf w.1) := by
  intro i j hij
  obtain ⟨hown, hdistinct⟩ := hQuant.geometry.star_distinct v heven
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some w => exact False.elim (hown w.1 w.2 hij.symm)
  | some w =>
    cases j with
    | none => exact False.elim (hown w.1 w.2 hij)
    | some z => congr 1; exact Subtype.ext (hdistinct w.1 w.2 z.1 z.2 hij)

/-- Initial list events depend only on the labels at external early incidences. -/
theorem gateBad_labels_congr {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (ys zs : Pos T k → Fin (T.S.N k))
    (h : ∀ w ∈ D.externalEarly v, ys w = zs w) :
    D.gateBad v σ ys ↔ D.gateBad v σ zs := by
  have hmass : D.rowMass v σ ys = D.rowMass v σ zs := by
    unfold ListGateContext.rowMass ListGateContext.row
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    exact Finset.prod_congr rfl (fun w hw => by rw [h w hw])
  have hlists : ∀ J, D.omittedList v J ys = D.omittedList v J zs := by
    intro J
    apply Finset.ext
    intro x
    simp only [ListGateContext.omittedList, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨hx, hh⟩
    · refine ⟨hx, fun w hw => ?_⟩
      rw [← h w (Finset.mem_sdiff.mp hw).1]
      exact hh w hw
    · refine ⟨hx, fun w hw => ?_⟩
      rw [h w (Finset.mem_sdiff.mp hw).1]
      exact hh w hw
  unfold ListGateContext.gateBad
  simp_rw [hmass, hlists]

/-- Data read at one star: its own fresh tape and one label from each other cell. -/
def StarDatum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k) :
    Option {w : Pos T k // w ∈ D.externalEarly v} → Type
  | none => D.F.State (D.G.cellOf v)
  | some _ => Fin (T.S.N k)

noncomputable instance starDatumFintype {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (i : Option {w : Pos T k // w ∈ D.externalEarly v}) : Fintype (StarDatum D v i) := by
  cases i <;> dsimp [StarDatum] <;> infer_instance

/-- The exact singleton marginal of one external fresh label. -/
noncomputable def externalLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (pools : D.PoolAssignment) (w : Pos T k) : FinLaw (Fin (T.S.N k)) :=
  FinLaw.map (D.F.fresh (D.G.cellOf w) (pools (D.G.cellOf w)))
    (fun s => D.F.label (D.G.cellOf w) s w)

noncomputable def starDatumLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (pools : D.PoolAssignment) :
    ∀ i, FinLaw (StarDatum D v i)
  | none => D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))
  | some w => externalLabelLaw D pools w.1

private theorem map_id {α : Type*} [Fintype α] (P : FinLaw α) :
    FinLaw.map P id = P := by
  classical
  apply finLaw_ext
  intro a
  simp [FinLaw.map]

/-- The list-event probability at fixed pools is exactly the probability in
the own-tape and independent external-singleton experiment. -/
theorem freshEventProbability_star {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (pools : D.PoolAssignment) :
    D.freshEventProbability v pools =
      (FinLaw.pi (starDatumLaw D v pools)).pr (fun z =>
        D.gateBad v (D.F.prior (D.G.cellOf v) (z none) v)
          (D.labelsOfPinnedSample v (T.S.N_pos k) (fun w => z (some w)))) := by
  classical
  let e : Option {w : Pos T k // w ∈ D.externalEarly v} → D.G.Cell :=
    fun i => match i with | none => D.G.cellOf v | some w => D.G.cellOf w.1
  let read : ∀ i, D.F.State (e i) → StarDatum D v i :=
    fun i => match i with | none => id | some w => fun s => D.F.label _ s w.1
  let f : (∀ i, StarDatum D v i) → ℝ := fun z =>
    if D.gateBad v (D.F.prior (D.G.cellOf v) (z none) v)
      (D.labelsOfPinnedSample v (T.S.N_pos k) (fun w => z (some w))) then 1 else 0
  have hpoint (s : Config D.F) :
      (if D.event v s then (1 : ℝ) else 0) = f (fun i => read i (s (e i))) := by
    have hg := gateBad_labels_congr D v (D.F.prior (D.G.cellOf v) (s (D.G.cellOf v)) v)
      (D.label s) (D.labelsOfPinnedSample v (T.S.N_pos k)
        (fun w => D.F.label (D.G.cellOf w.1) (s (D.G.cellOf w.1)) w.1))
      (fun w hw => by simp [ListGateContext.label, ListGateContext.labelsOfPinnedSample, hw])
    simpa [f, read, e, ListGateContext.event, ListGateContext.prior, heven] using
      (if_congr hg rfl rfl :
        (if D.gateBad v (D.F.prior (D.G.cellOf v) (s (D.G.cellOf v)) v) (D.label s)
          then (1 : ℝ) else 0) = _)
  have hlaws : (fun i => FinLaw.map (D.F.fresh (e i) (pools (e i))) (read i)) =
      starDatumLaw D v pools := by
    funext i
    cases i with
    | none => exact map_id _
    | some w =>
      apply finLaw_ext
      intro y
      simp only [e, read, starDatumLaw, externalLabelLaw, FinLaw.map]
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs with h₁ h₂ <;> simp_all [StarDatum]
      exact False.elim (h₁ rfl)
  calc
    D.freshEventProbability v pools = (D.freshConfigLaw pools).E
        (fun s => if D.event v s then 1 else 0) := by
      unfold ListGateContext.freshEventProbability FinLaw.pr FinLaw.E
      apply Finset.sum_congr rfl
      intro s hs
      by_cases h : D.event v s <;> simp [h]
    _ = (D.freshConfigLaw pools).E (fun s => f (fun i => read i (s (e i)))) := by
      congr 1
      funext s
      exact hpoint s
    _ = (FinLaw.pi (starDatumLaw D v pools)).E f := by
      unfold ListGateContext.freshConfigLaw
      rw [pi_E_injective_readouts _ e (star_cells_injective D K hQuant v heven) read f, hlaws]
      unfold FinLaw.E FinLaw.pi
      congr! 2
    _ = _ := by
      unfold FinLaw.pr FinLaw.E
      apply Finset.sum_congr rfl
      intro z hz
      dsimp [f]
      split_ifs with h <;> simp [h]

/-- Physical-bin count times bin size is the patch mass. -/
theorem bins_count_mul_size {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    Fintype.card (Bin PT.tiling i) * (PT.tiling.P i).d = (PT.tiling.P i).M := by
  have h := (PT.tiling.P i).bins.sum_card_parts
  have hs : (∑ B ∈ (PT.tiling.P i).bins.parts, B.card) =
      (PT.tiling.P i).bins.parts.card * (PT.tiling.P i).d := by
    calc
      _ = ∑ _B ∈ (PT.tiling.P i).bins.parts, (PT.tiling.P i).d :=
        Finset.sum_congr rfl (fun B hB => hPT.tiling_valid.bins_card i B hB)
      _ = _ := by simp
  rw [hs, (PT.tiling.P i).cardY] at h
  change Fintype.card {B // B ∈ (PT.tiling.P i).bins.parts} * (PT.tiling.P i).d = _
  rw [Fintype.card_coe]
  exact h

/-- Weight after a uniformly chosen actual slot, including its permission test. -/
noncomputable def externalSlotWeight {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (b : Pos T k)
    (P : D.F.Pool (D.G.cellOf b)) (j : Fin (D.G.nslot (D.G.cellOf b)))
    (y : Fin (T.S.N k)) : ℝ :=
  (Fintype.card (Bin PT.tiling (D.G.patchOf b)) : ℝ) *
    (PT.π (D.G.patchOf b)).w y *
    if y ∈ (P j).1 ∧ hQuant.sampler.permittedBin b
      (cast (by rw [D.G.cellOf_patch]) (P j)) then 1 else 0

theorem externalSlotWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (b : Pos T k)
    (P : D.F.Pool (D.G.cellOf b)) (j : Fin (D.G.nslot (D.G.cellOf b)))
    (y : Fin (T.S.N k)) : 0 ≤ externalSlotWeight D K hQuant b P j y := by
  unfold externalSlotWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ((PT.π _).nonneg _))
    (by split_ifs <;> norm_num)

/-- L16's external singleton bound is dominated by the average over actual
slots, even when several iid slots have the same bin image. -/
theorem singleton_le_slot_average {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (b : Pos T k)
    (pools : D.PoolAssignment) (htyp : D.F.typical (D.G.cellOf b) (pools (D.G.cellOf b)))
    (hodd : ¬ IsEvenRole b) (hL : 0 < D.G.nslot (D.G.cellOf b))
    (y : Fin (T.S.N k)) :
    (externalLabelLaw D pools b).w y ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) *
        ((∑ j, externalSlotWeight D K hQuant b (pools (D.G.cellOf b)) j y) /
          (D.G.nslot (D.G.cellOf b) : ℝ)) := by
  classical
  let Q : Fin (D.G.nslot (D.G.cellOf b)) → Prop := fun j =>
    y ∈ (pools (D.G.cellOf b) j).1 ∧ hQuant.sampler.permittedBin b
      (cast (by rw [D.G.cellOf_patch]) (pools (D.G.cellOf b) j))
  have hpresent : y ∈ D.permittedLabels (D.G.cellOf b) (pools (D.G.cellOf b)) b ↔
      ∃ j, Q j := hQuant.sampler.permission_present _ _ b rfl y
  have hcount : (if y ∈ D.permittedLabels (D.G.cellOf b) (pools (D.G.cellOf b)) b
      then (1 : ℝ) else 0) ≤ ∑ j, if Q j then (1 : ℝ) else 0 := by
    by_cases hp : y ∈ D.permittedLabels (D.G.cellOf b) (pools (D.G.cellOf b)) b
    · obtain ⟨j, hj⟩ := hpresent.mp hp
      simpa [hp, hj] using (Finset.single_le_sum (f := fun i => if Q i then (1 : ℝ) else 0)
        (fun i (_ : i ∈ Finset.univ) => by split_ifs <;> norm_num)
        (Finset.mem_univ j) :
        (if Q j then (1 : ℝ) else 0) ≤ ∑ i, if Q i then (1 : ℝ) else 0)
    · simp only [hp, ite_false]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hB : 0 ≤ (Fintype.card (Bin PT.tiling (D.G.patchOf b)) : ℝ) := Nat.cast_nonneg _
  have hLreal : 0 < (D.G.nslot (D.G.cellOf b) : ℝ) := by exact_mod_cast hL
  have hε : 0 ≤ 1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hbound := hQuant.singleton_bound _ _ b y htyp rfl hodd
  rw [hQuant.geometry.slot_factor_eq b] at hbound
  change (FinLaw.map _ _).w y ≤ _
  rw [map_weight_eq_pr]
  refine hbound.trans ?_
  have havg : (∑ j, externalSlotWeight D K hQuant b (pools (D.G.cellOf b)) j y) =
      (Fintype.card (Bin PT.tiling (D.G.patchOf b)) : ℝ) * (PT.π (D.G.patchOf b)).w y *
        (∑ j, if Q j then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    rfl
  rw [havg]
  have hh := mul_le_mul_of_nonneg_left hcount
    (mul_nonneg hB ((PT.π (D.G.patchOf b)).nonneg y))
  have hd := div_le_div_of_nonneg_right hh hLreal.le
  have hm := mul_le_mul_of_nonneg_left hd hε
  convert hm using 1 <;> ring

/-- A selected slot costs at most eleven after summing all its possible labels. -/
theorem externalSlotWeight_total_le_eleven {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (b : Pos T k)
    (P : D.F.Pool (D.G.cellOf b)) (j : Fin (D.G.nslot (D.G.cellOf b))) :
    (∑ y, externalSlotWeight D K hQuant b P j y) ≤ 11 := by
  classical
  let i := D.G.patchOf b
  let B : Bin PT.tiling i := cast (by rw [D.G.cellOf_patch]) (P j)
  have hMnat : 0 < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact Finset.card_pos.mpr (D.tiling_valid.tiling_valid.patch_nonempty i).1
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by exact_mod_cast hMnat
  have hBinCard : (P j).1.card = (PT.tiling.P i).d := by
    simpa [i, D.G.cellOf_patch] using
      D.tiling_valid.tiling_valid.bins_card (D.G.cellPatch (D.G.cellOf b)) (P j).1 (P j).2
  have hcount : (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d =
      (PT.tiling.P i).M := by exact_mod_cast bins_count_mul_size D.tiling_valid i
  calc
    _ ≤ ∑ y ∈ (P j).1,
        (Fintype.card (Bin PT.tiling i) : ℝ) * (11 / (PT.tiling.P i).M) := by
      have hs : (∑ y ∈ (P j).1,
          (Fintype.card (Bin PT.tiling i) : ℝ) * (11 / (PT.tiling.P i).M)) =
          ∑ y, if y ∈ (P j).1 then
            (Fintype.card (Bin PT.tiling i) : ℝ) * (11 / (PT.tiling.P i).M) else 0 := by
        simp only [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hs]
      apply Finset.sum_le_sum
      intro y hy
      unfold externalSlotWeight
      by_cases hmem : y ∈ (P j).1
      · simp only [hmem, ite_true]
        split_ifs
        · simpa [i] using mul_le_mul_of_nonneg_left (D.tiling_valid.law_cap i y)
            (Nat.cast_nonneg (Fintype.card (Bin PT.tiling i)))
        · simp only [mul_zero]
          exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by norm_num) hM.le)
      · simp [hmem]
    _ = ((PT.tiling.P i).d : ℝ) *
        ((Fintype.card (Bin PT.tiling i) : ℝ) * (11 / (PT.tiling.P i).M)) := by
      simp [hBinCard]
    _ = 11 := by
      rw [mul_left_comm, ← mul_assoc, hcount]
      field_simp

/-- Averaging an unforced uniform bin restores the comparison label law. -/
theorem uniform_bin_restores_label {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (hB : (Finset.univ : Finset (Bin PT.tiling i)).Nonempty)
    (y : Fin (T.S.N k)) :
    (FinLaw.uniform Finset.univ hB).E (fun B =>
      (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.π i).w y *
        (if y ∈ B.1 then 1 else 0)) = (PT.π i).w y := by
  classical
  have hcard : (Fintype.card (Bin PT.tiling i) : ℝ) ≠ 0 := by
    exact_mod_cast (by simpa using (Finset.card_pos.mpr hB).ne' :
      Fintype.card (Bin PT.tiling i) ≠ 0)
  by_cases hy : y ∈ (PT.tiling.P i).Y
  · obtain ⟨B, hBmem, hyB⟩ := (PT.tiling.P i).bins.exists_mem hy
    let B' : Bin PT.tiling i := ⟨B, hBmem⟩
    unfold FinLaw.E
    rw [Finset.sum_eq_single B']
    · simp [FinLaw.uniform, B', hyB]
      field_simp
    · intro C hC hne
      have hny : y ∉ C.1 := by
        intro hyC
        apply hne
        apply Subtype.ext
        exact (PT.tiling.P i).bins.eq_of_mem_parts C.2 hBmem hyC hyB
      simp [hny]
    · simp
  · simp [hPT.law_supported i y hy, FinLaw.E]

end HypercubeRamsey.Lane_sol_s17_pool
