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

/-- At a fixed pool the full experiment is an own-tape sum followed by a
product of external singleton atoms. -/
theorem freshEventProbability_star_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (pools : D.PoolAssignment) :
    D.freshEventProbability v pools =
      ∑ s : D.F.State (D.G.cellOf v),
        (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).w s *
          ∑ ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
            (∏ w, (externalLabelLaw D pools w.1).w (ys w)) *
              if D.gateBad v (D.F.prior (D.G.cellOf v) s v)
                (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then 1 else 0 := by
  classical
  rw [freshEventProbability_star D K hQuant v heven pools]
  unfold FinLaw.pr
  let e := Equiv.piOptionEquivProd (β := StarDatum D v)
  let f : (∀ i, StarDatum D v i) → ℝ := fun z =>
    if D.gateBad v (D.F.prior (D.G.cellOf v) (z none) v)
      (D.labelsOfPinnedSample v (T.S.N_pos k) (fun w => z (some w))) then
        (FinLaw.pi (starDatumLaw D v pools)).w z else 0
  change (∑ z, f z) = _
  have heq : (∑ z, f z) = ∑ p, f (e.symm p) :=
    Fintype.sum_equiv e f (fun p => f (e.symm p)) (fun z => by simp)
  rw [heq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  change (if D.gateBad v (D.F.prior (D.G.cellOf v) s v)
      (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then
        ∏ i, (starDatumLaw D v pools i).w
          ((Equiv.piOptionEquivProd (β := StarDatum D v)).symm (s, ys) i) else 0) = _
  rw [Fintype.prod_option]
  by_cases h : D.gateBad v (D.F.prior (D.G.cellOf v) s v)
      (D.labelsOfPinnedSample v (T.S.N_pos k) ys)
  · simp [h, starDatumLaw, Equiv.piOptionEquivProd]
  · simp [h]

/-- The product of actual slot weights averages into the product of the
singleton slot averages. -/
theorem slot_average_product {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (pools : D.PoolAssignment)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w))
    (ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :
    (FinLaw.pi (fun w : {w : Pos T k // w ∈ D.externalEarly v} =>
      FinLaw.uniform (Finset.univ : Finset (Fin (D.G.nslot (D.G.cellOf w.1))))
        ⟨⟨0, hL w.1 w.2⟩, Finset.mem_univ _⟩)).E (fun slots =>
          ∏ w, externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) (slots w) (ys w)) =
      ∏ w, (∑ j, externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) j (ys w)) /
        (D.G.nslot (D.G.cellOf w.1) : ℝ) := by
  classical
  let P : ∀ w : {w : Pos T k // w ∈ D.externalEarly v},
      FinLaw (Fin (D.G.nslot (D.G.cellOf w.1))) := fun w =>
    FinLaw.uniform Finset.univ ⟨⟨0, hL w.1 w.2⟩, Finset.mem_univ _⟩
  change (FinLaw.pi P).E (fun slots =>
    ∏ w, externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) (slots w) (ys w)) = _
  rw [Lane_q_s17_pool.pi_expect_prod P
    (fun w j => externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) j (ys w))]
  apply Finset.prod_congr rfl
  intro w hw
  unfold FinLaw.E P
  simp only [FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.mul_sum]
  ring

/-- Expanding the fresh star and using all singleton comparisons gives the
actual independently selected-slot experiment, with one error factor per
external incidence. -/
theorem fresh_star_slot_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (pools : D.PoolAssignment)
    (htyp : D.LocalPoolsTypical v pools)
    (hodd : ∀ w ∈ D.externalEarly v, ¬ IsEvenRole w)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w)) :
    D.freshEventProbability v pools ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ (D.externalEarly v).card *
        ∑ s : D.F.State (D.G.cellOf v),
          (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).w s *
            ∑ ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
              (FinLaw.pi (fun w : {w : Pos T k // w ∈ D.externalEarly v} =>
                FinLaw.uniform (Finset.univ : Finset (Fin (D.G.nslot (D.G.cellOf w.1))))
                  ⟨⟨0, hL w.1 w.2⟩, Finset.mem_univ _⟩)).E (fun slots =>
                    ∏ w, externalSlotWeight D K hQuant w.1
                      (pools (D.G.cellOf w.1)) (slots w) (ys w)) *
                if D.gateBad v (D.F.prior (D.G.cellOf v) s v)
                  (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then 1 else 0 := by
  classical
  let ε : ℝ := 1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)
  have hε : 0 ≤ ε := add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hExtTyp (w : {w : Pos T k // w ∈ D.externalEarly v}) :
      D.F.typical (D.G.cellOf w.1) (pools (D.G.cellOf w.1)) :=
    htyp _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩)))
  rw [freshEventProbability_star_sum D K hQuant v heven pools, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ ((D.F.fresh _ _).nonneg s)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ys hys
  let A : {w : Pos T k // w ∈ D.externalEarly v} → ℝ := fun w =>
    (∑ j, externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) j (ys w)) /
      (D.G.nslot (D.G.cellOf w.1) : ℝ)
  have hprod : (∏ w, (externalLabelLaw D pools w.1).w (ys w)) ≤
      ε ^ (D.externalEarly v).card * ∏ w, A w := by
    calc
      _ ≤ ∏ w, ε * A w := by
        apply Finset.prod_le_prod₀
        · intro w hw
          exact (externalLabelLaw D pools w.1).nonneg (ys w)
        · intro w hw
          exact singleton_le_slot_average D K hQuant w.1 pools (hExtTyp w)
            (hodd w.1 w.2) (hL w.1 w.2) (ys w)
      _ = ε ^ (D.externalEarly v).card * ∏ w, A w := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have hAvg := slot_average_product D K hQuant v pools hL ys
  dsimp [A] at hprod
  rw [← Finset.univ_eq_attach] at hprod
  rw [← hAvg] at hprod
  have hh := mul_le_mul_of_nonneg_right hprod
    (show 0 ≤ (if D.gateBad v (D.F.prior (D.G.cellOf v) s v)
      (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then (1 : ℝ) else 0) by split_ifs <;> norm_num)
  convert hh using 1 <;> ring

/-- Every actual slot in the cell scope of one star. -/
noncomputable def starSlots {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k) :
    Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)) :=
  (D.scopeCells v).sigma (fun _ => Finset.univ)

theorem starSlots_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (hn : 2 ≤ T.S.n k) : (starSlots D v).card ≤ (T.S.n k) ^ (κ.Ac + 4) := by
  classical
  let n := T.S.n k
  have hscope : (D.scopeCells v).card ≤ n + 1 := by
    unfold ListGateContext.scopeCells
    calc
      _ ≤ ({D.G.cellOf v} : Finset D.G.Cell).card +
          ((D.externalEarly v).image D.G.cellOf).card := Finset.card_union_le _ _
      _ ≤ 1 + (D.externalEarly v).card := by
        simp only [Finset.card_singleton]
        exact Nat.add_le_add_left (Finset.card_image_le) 1
      _ ≤ n + 1 := by have he := Lane_q_s17_pool.externalEarly_card_le D v; omega
  have hslots (C : D.G.Cell) : D.G.nslot C ≤ n ^ (κ.Ac + 1) := by
    have hh := hQuant.geometry.slots_upper C
    rw [show (κ.Ac : ℝ) + 1 = ((κ.Ac + 1 : ℕ) : ℝ) by push_cast; rfl] at hh
    change (D.G.nslot C : ℝ) ≤ (T.S.n k : ℝ) ^ ((κ.Ac + 1 : ℕ) : ℝ) at hh
    rw [Real.rpow_natCast (T.S.n k : ℝ) (κ.Ac + 1)] at hh
    exact_mod_cast hh
  unfold starSlots
  rw [Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_fin]
  calc
    _ ≤ ∑ _C ∈ D.scopeCells v, n ^ (κ.Ac + 1) :=
      Finset.sum_le_sum (fun C _ => hslots C)
    _ = (D.scopeCells v).card * n ^ (κ.Ac + 1) := by simp
    _ ≤ (n + 1) * n ^ (κ.Ac + 1) := Nat.mul_le_mul_right _ hscope
    _ ≤ n ^ 2 * n ^ (κ.Ac + 1) := by
      apply Nat.mul_le_mul_right
      dsimp [n] at hn ⊢
      nlinarith
    _ = n ^ (κ.Ac + 3) := by rw [← pow_add]; congr 1; omega
    _ ≤ n ^ (κ.Ac + 4) := Nat.pow_le_pow_right (by dsimp [n]; omega) (by omega)

/-- Reading all slots of the local scope is still polynomially small, so
the quantitative producer comparison applies directly to any local pool test. -/
theorem local_pool_iid_comparison {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (hn : 2 ≤ T.S.n k) (μ : FinLaw D.PoolAssignment)
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ) :
    ∃ ν : FinLaw D.PoolAssignment,
      (ν = iidPoolLaw D.G hQuant.pool_support_nonempty ∨
        ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
          (iidPoolLaw D.G hQuant.pool_support_nonempty).w pools),
          ν = FinLaw.cond (iidPoolLaw D.G hQuant.pool_support_nonempty) (D.poolPinSet pin) hpin) ∧
      ∀ f : D.PoolAssignment → ℝ, (∀ pools, 0 ≤ f pools) →
        (∀ p q, (∀ C ∈ D.scopeCells v, p C = q C) → f p = f q) →
        μ.E f ≤ (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) * ν.E f := by
  obtain ⟨ν, hν, hcompare⟩ := hQuant.pool_iid_comparison μ hμ
  refine ⟨ν, hν, fun f hf hlocal => ?_⟩
  apply hcompare (starSlots D v) f (starSlots_card_le D K hQuant v hn) hf
  intro p q hslots
  apply hlocal p q
  intro C hC
  funext j
  exact hslots ⟨C, j⟩ (by simp [starSlots, Finset.mem_sigma, hC])

/-- The local typicality and compatibility tests read only pools in the star scope. -/
theorem pool_predicates_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (p q : D.PoolAssignment) (h : ∀ C ∈ D.scopeCells v, p C = q C) :
    (D.LocalPoolsTypical v p ↔ D.LocalPoolsTypical v q) ∧
      (D.compatiblePool v p ↔ D.compatiblePool v q) := by
  classical
  have ho : p (D.G.cellOf v) = q (D.G.cellOf v) := h _ (by simp [ListGateContext.scopeCells])
  have he (w : Pos T k) (hw : w ∈ D.externalEarly v) :
      p (D.G.cellOf w) = q (D.G.cellOf w) :=
    h _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)))
  constructor
  · constructor
    · intro ht C hC
      rw [← h C hC]
      exact ht C hC
    · intro ht C hC
      rw [h C hC]
      exact ht C hC
  · constructor
    · intro hc pins hpins hcard fixed hperm
      have hf : ∀ w ∈ pins, fixed w ∈ D.permittedLabels (D.G.cellOf w) (p (D.G.cellOf w)) w := by
        intro w hw
        rw [he w (hpins hw)]
        exact hperm w hw
      simpa only [ho] using hc pins hpins hcard fixed hf
    · intro hc pins hpins hcard fixed hperm
      have hf : ∀ w ∈ pins, fixed w ∈ D.permittedLabels (D.G.cellOf w) (q (D.G.cellOf w)) w := by
        intro w hw
        rw [← he w (hpins hw)]
        exact hperm w hw
      simpa only [ho] using hc pins hpins hcard fixed hf

/-- The exact fresh star probability also depends only on the local pool scope. -/
theorem fresh_probability_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k) (heven : IsEvenRole v)
    (p q : D.PoolAssignment) (h : ∀ C ∈ D.scopeCells v, p C = q C) :
    D.freshEventProbability v p = D.freshEventProbability v q := by
  classical
  have ho : p (D.G.cellOf v) = q (D.G.cellOf v) := h _ (by simp [ListGateContext.scopeCells])
  have he (w : {w : Pos T k // w ∈ D.externalEarly v}) :
      externalLabelLaw D p w.1 = externalLabelLaw D q w.1 := by
    unfold externalLabelLaw
    rw [h _ (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩)))]
  rw [freshEventProbability_star_sum D K hQuant v heven p,
    freshEventProbability_star_sum D K hQuant v heven q, ho]
  simp_rw [he]

/-- The permutation-pool repeated-trial moment reduces to a raw or one-pin
iid experiment with the producer's single comparison factor. -/
theorem trial_moment_iid_reduction {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k) (heven : IsEvenRole v)
    (hn : 2 ≤ T.S.n k) (μ : FinLaw D.PoolAssignment)
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ) (m : ℕ) :
    ∃ ν : FinLaw D.PoolAssignment,
      (ν = iidPoolLaw D.G hQuant.pool_support_nonempty ∨
        ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
          (iidPoolLaw D.G hQuant.pool_support_nonempty).w pools),
          ν = FinLaw.cond (iidPoolLaw D.G hQuant.pool_support_nonempty) (D.poolPinSet pin) hpin) ∧
      μ.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
          (D.freshEventProbability v pools) ^ m else 0) ≤
        (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) *
          ν.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
            (D.freshEventProbability v pools) ^ m else 0) := by
  classical
  obtain ⟨ν, hν, hcompare⟩ := local_pool_iid_comparison D K hQuant v hn μ hμ
  refine ⟨ν, hν, hcompare _ ?_ ?_⟩
  · intro pools
    split_ifs
    · apply pow_nonneg
      unfold ListGateContext.freshEventProbability FinLaw.pr
      exact Finset.sum_nonneg (fun s _ => by split_ifs; exact (D.freshConfigLaw pools).nonneg s; exact le_rfl)
    · exact le_rfl
  · intro p q hlocal
    obtain ⟨ht, hc⟩ := pool_predicates_local D v p q hlocal
    have hf := fresh_probability_local D K hQuant v heven p q hlocal
    simp only [ht, hc, hf]

/-- Uniform independent coordinates give the uniform law on all assignments. -/
theorem uniform_pi {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (hΩ : ∀ i, (Finset.univ : Finset (Ω i)).Nonempty)
    (hAll : (Finset.univ : Finset (∀ i, Ω i)).Nonempty) :
    FinLaw.pi (fun i => FinLaw.uniform Finset.univ (hΩ i)) =
      FinLaw.uniform Finset.univ hAll := by
  classical
  apply finLaw_ext
  intro s
  simp only [FinLaw.pi, FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ]
  rw [Fintype.card_pi]
  push_cast
  rw [Finset.prod_div_distrib]
  simp

/-- A coordinate pin in a product law leaves all other coordinates independent. -/
theorem pi_condition_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (j : I) (y : Ω j)
    (hp : 0 < ∑ s ∈ Finset.univ.filter (fun s : ∀ i, Ω i => s j = y), (FinLaw.pi P).w s) :
    FinLaw.cond (FinLaw.pi P) (Finset.univ.filter (fun s : ∀ i, Ω i => s j = y)) hp =
      FinLaw.pi (fun i => if h : i = j then
        (h.symm ▸ FinLaw.dirac y : FinLaw (Ω i)) else P i) := by
  classical
  let base : ∀ i, Ω i := Classical.choice (S16.Lane_q_s16_comp2.nonempty_of_finLaw (FinLaw.pi P))
  let z := Function.update base j y
  have hcoord : (FinLaw.pi P).pr (fun s => s j = y) = (P j).w y := by
    have h := S16.Lane_q_s16_comp2.pi_pr_cylinder P {j} z
    simpa [z] using h
  have hMass : (∑ s ∈ Finset.univ.filter (fun s : ∀ i, Ω i => s j = y), (FinLaw.pi P).w s) =
      (P j).w y := by
    simpa [FinLaw.pr, Finset.sum_filter] using hcoord
  have hpy : 0 < (P j).w y := hMass ▸ hp
  apply finLaw_ext
  intro s
  simp only [FinLaw.cond, hMass, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hsy : s j = y
  · simp only [hsy, ite_true]
    change (∏ i, (P i).w (s i)) / (P j).w y =
      ∏ i, (if h : i = j then (h.symm ▸ FinLaw.dirac y : FinLaw (Ω i)) else P i).w (s i)
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [dite_true, FinLaw.dirac, hsy, ite_true, mul_one]
    have hOther : (∏ i ∈ Finset.univ.erase j,
        (if h : i = j then (h.symm ▸ FinLaw.dirac y : FinLaw (Ω i)) else P i).w (s i)) =
        ∏ i ∈ Finset.univ.erase j, (P i).w (s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.ne_of_mem_erase hi]
    exact (mul_div_cancel_right₀ _ hpy.ne').trans (by
      simpa only [FinLaw.dirac] using hOther.symm)
  · simp only [hsy, ite_false, zero_div]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [FinLaw.dirac, hsy]

end HypercubeRamsey.Lane_sol_s17_pool
