import HypercubeRamsey.S13.ResidualBounds
import Mathlib.Analysis.Complex.ExponentialBounds

namespace HypercubeRamsey.S13

open scoped BigOperators
open Filter

/-- Partition the initial `d`-blocks of a finite set, leaving only its final remainder. -/
theorem allocation_chunks_exact {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (d : ℕ) (hd : 0 < d) :
    ∃ C : Fin (B.card / d) → Finset α,
      (∀ i, C i ⊆ B) ∧
      (∀ i, (C i).card = d) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      (Finset.univ.biUnion C).card = (B.card / d) * d := by
  classical
  let e : {x : α // x ∈ B} ≃ Fin B.card :=
    Fintype.equivFinOfCardEq (by simp)
  let emb : Fin B.card ↪ α :=
    ⟨fun x => (e.symm x).val, by
      intro x y h
      have hs : e.symm x = e.symm y := Subtype.ext h
      exact e.symm.injective hs⟩
  have interval_card (lo hi : ℕ) (hlo : lo ≤ hi) (hhi : hi ≤ B.card) :
      (Finset.univ.filter fun x : Fin B.card => lo ≤ x.val ∧ x.val < hi).card = hi - lo := by
    let f : {x : ℕ // x ∈ Finset.Ico lo hi} ↪ Fin B.card :=
      ⟨fun x => ⟨x.val, (Finset.mem_Ico.mp x.property).2.trans_le hhi⟩, by
        intro x y h
        apply Subtype.ext
        exact congrArg Fin.val h⟩
    have himage : (Finset.Ico lo hi).attach.map f =
        Finset.univ.filter fun x : Fin B.card => lo ≤ x.val ∧ x.val < hi := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
        have hy' : y.val ∈ Finset.Ico lo hi := y.property
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_Ico.mp hy').1,
          (Finset.mem_Ico.mp hy').2⟩
      · intro hx
        rcases Finset.mem_filter.mp hx with ⟨_, hloX, hhiX⟩
        let y : {y : ℕ // y ∈ Finset.Ico lo hi} :=
          ⟨x.val, Finset.mem_Ico.mpr ⟨hloX, hhiX⟩⟩
        refine Finset.mem_map.mpr ⟨y, Finset.mem_attach (Finset.Ico lo hi) y, ?_⟩
        exact Fin.ext rfl
    rw [← himage, Finset.card_map, Finset.card_attach]
    simp
  let C : Fin (B.card / d) → Finset α := fun i =>
    (Finset.univ.filter fun x : Fin B.card =>
      i.val * d ≤ x.val ∧ x.val < (i.val + 1) * d).map emb
  have hupper (i : Fin (B.card / d)) : (i.val + 1) * d ≤ B.card := by
    have hi : i.val + 1 ≤ B.card / d := by omega
    calc
      _ ≤ (B.card / d) * d := Nat.mul_le_mul_right d hi
      _ ≤ B.card := Nat.div_mul_le_self _ _
  have hcard (i : Fin (B.card / d)) : (C i).card = d := by
    dsimp [C]
    rw [Finset.card_map]
    have hlo : i.val * d ≤ (i.val + 1) * d :=
      Nat.mul_le_mul_right d (Nat.le_succ _)
    rw [interval_card (i.val * d) ((i.val + 1) * d) hlo (hupper i)]
    rw [Nat.add_mul, one_mul]
    omega
  have hsub (i : Fin (B.card / d)) : C i ⊆ B := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact (e.symm y).property
  have hdisj (i j : Fin (B.card / d)) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    rcases Finset.mem_map.mp hxi with ⟨a, ha, hax⟩
    rcases Finset.mem_map.mp hxj with ⟨b, hb, hbx⟩
    have hab : a = b := emb.injective (hax.trans hbx.symm)
    subst b
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hgap : (i.val + 1) * d ≤ j.val * d :=
        Nat.mul_le_mul_right d (by omega)
      omega
    · have hgap : (j.val + 1) * d ≤ i.val * d :=
        Nat.mul_le_mul_right d (by omega)
      omega
  have hUnion : (Finset.univ.biUnion C).card = (B.card / d) * d := by
    rw [Finset.card_biUnion]
    · simp_rw [hcard]
      simp [Finset.sum_const, nsmul_eq_mul]
    · intro i hi j hj hij
      exact hdisj i j hij
  exact ⟨C, hsub, hcard, hdisj, hUnion⟩

/-- A host of dimension `n` has enough labels for the exact-size subsampler. -/
theorem allocation_sample_growth (T : Stage) :
    ∀ᶠ k in atTop,
      (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤
        (2 : ℝ) ^ T.S.n k * Real.exp (-(T.S.n k : ℝ) / 4) := by
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hnSeq : Tendsto (fun k : ℕ => (T.S.n k : ℝ) / 4) atTop atTop := by
    have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
    have ht' : Tendsto (fun k : ℕ => (1 / 4 : ℝ) * (T.S.n k : ℝ)) atTop atTop :=
      ht.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    simpa [div_eq_mul_inv, mul_comm] using ht'
  have hgrowthTendsto := (Real.tendsto_exp_div_pow_atTop 12).comp hnSeq
  have hgrowthEvent : ∀ᶠ k in atTop,
      16 * (4 : ℝ) ^ 12 ≤ Real.exp ((T.S.n k : ℝ) / 4) /
        ((T.S.n k : ℝ) / 4) ^ 12 := by
    have h := hgrowthTendsto.eventually (eventually_ge_atTop (16 * (4 : ℝ) ^ 12))
    filter_upwards [h] with k hk
    exact hk
  have hlarge := T.S.eventually_large 1 16
  filter_upwards [hlarge, hgrowthEvent] with k hk hg
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  have hmul :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < ((T.S.n k : ℝ) / 4) ^ 12)).mp hg
  have hcancel : (4 : ℝ) ^ 12 * ((T.S.n k : ℝ) / 4) ^ 12 =
      (T.S.n k : ℝ) ^ 12 := by field_simp [ne_of_gt hnpos] <;> ring
  have hexpLower : (16 : ℝ) * (T.S.n k : ℝ) ^ 12 ≤
      Real.exp ((T.S.n k : ℝ) / 4) := by
    calc
      _ = 16 * ((4 : ℝ) ^ 12 * ((T.S.n k : ℝ) / 4) ^ 12) := by rw [hcancel]
      _ = 16 * (4 : ℝ) ^ 12 * ((T.S.n k : ℝ) / 4) ^ 12 := by ring
      _ ≤ Real.exp ((T.S.n k : ℝ) / 4) := hmul
  have htwo : Real.exp ((T.S.n k : ℝ) / 2) ≤ (2 : ℝ) ^ T.S.n k := by
    calc
      Real.exp ((T.S.n k : ℝ) / 2) ≤
          Real.exp ((T.S.n k : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith [hlogTwo])
      _ = (2 : ℝ) ^ T.S.n k := by
        rw [Real.exp_nat_mul]
        simp [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsplit : Real.exp ((T.S.n k : ℝ) / 2) *
      Real.exp (-(T.S.n k : ℝ) / 4) = Real.exp ((T.S.n k : ℝ) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right htwo
    (Real.exp_nonneg (-(T.S.n k : ℝ) / 4))
  rw [hsplit] at hmul
  have hresult := le_trans hexpLower hmul
  simpa using hresult

/-- A uniform core law turns a finite expectation into a normalized finite sum. -/
theorem allocation_unifCore_sum {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty)
    (f : Fin N → ℝ) :
    ∑ x, (Law.unifCore A hA).w x * f x = (∑ x ∈ A, f x) / A.card := by
  classical
  change (∑ x, (if x ∈ A then (A.card : ℝ)⁻¹ else 0) * f x) = _
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
  rw [div_eq_mul_inv]
  ring

/-- Find the first list prefix whose weights reach a positive threshold. -/
theorem allocation_exists_prefix_cross {α : Type*} (w : α → ℝ) (t : ℝ) (ht : 0 < t)
    (l : List α) (hsum : t ≤ (l.map w).sum) :
    ∃ pre a tail, l = pre ++ a :: tail ∧
      (pre.map w).sum < t ∧ t ≤ (pre.map w).sum + w a := by
  induction l generalizing t with
  | nil => simp at hsum; linarith
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons] at hsum
      by_cases hhead : t ≤ w a
      · refine ⟨[], a, l, rfl, by simp [ht], ?_⟩
        simpa using hhead
      · have hhead' : w a < t := lt_of_not_ge hhead
        have htail : t - w a ≤ (l.map w).sum := by linarith
        obtain ⟨pre, b, tail, hdecomp, hpre, hcross⟩ :=
          ih (t - w a) (sub_pos.mpr hhead') htail
        refine ⟨a :: pre, b, tail, ?_, ?_, ?_⟩
        · simp [hdecomp]
        · simp only [List.map_cons, List.sum_cons]
          linarith
        · simp only [List.map_cons, List.sum_cons]
          linarith

/-- Rounding `log₂ r` down gives the two adjacent dyadic bounds for `1/r`. -/
noncomputable def allocation_roundLength (r : ℝ) : ℕ :=
  ⌊Real.log r / Real.log 2⌋₊

theorem allocation_dyadicRoundLength_bounds (r : ℝ) (hr : 1 ≤ r) :
    r⁻¹ ≤ (2 : ℝ) ^ (-(allocation_roundLength r : ℤ)) ∧
      (2 : ℝ) ^ (-(allocation_roundLength r : ℤ)) < 2 * r⁻¹ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  let z : ℝ := Real.log r / Real.log 2
  have hz : 0 ≤ z := div_nonneg hlogr hlog2.le
  have hfloorLo : (allocation_roundLength r : ℝ) ≤ z := by
    exact Nat.floor_le hz
  have hfloorHi : z < (allocation_roundLength r : ℝ) + 1 := by
    simpa [allocation_roundLength] using (Nat.lt_succ_floor z)
  have hlogLo : (allocation_roundLength r : ℝ) * Real.log 2 ≤ Real.log r := by
    have h := (le_div_iff₀ hlog2).mp hfloorLo
    simpa [z, mul_comm] using h
  have hlogHi : Real.log r <
      ((allocation_roundLength r : ℝ) + 1) * Real.log 2 := by
    have h := (div_lt_iff₀ hlog2).mp hfloorHi
    simpa [z, mul_comm] using h
  have hExpPow (n : ℕ) : Real.exp ((n : ℝ) * Real.log 2) = (2 : ℝ) ^ n := by
    rw [Real.exp_nat_mul]
    simp [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hratioLo : (2 : ℝ) ^ allocation_roundLength r ≤ r := by
    calc
      _ = Real.exp ((allocation_roundLength r : ℝ) * Real.log 2) := (hExpPow _).symm
      _ ≤ Real.exp (Real.log r) := Real.exp_le_exp.mpr hlogLo
      _ = r := Real.exp_log (by positivity)
  have hratioHi : r < (2 : ℝ) ^ (allocation_roundLength r + 1) := by
    calc
      r = Real.exp (Real.log r) := (Real.exp_log (by positivity)).symm
      _ < Real.exp (((allocation_roundLength r : ℝ) + 1) * Real.log 2) :=
        Real.exp_lt_exp.mpr hlogHi
      _ = (2 : ℝ) ^ (allocation_roundLength r + 1) := by
        rw [show (allocation_roundLength r : ℝ) + 1 =
          ((allocation_roundLength r + 1 : ℕ) : ℝ) by norm_num]
        exact hExpPow (allocation_roundLength r + 1)
  have hposPow (n : ℕ) : 0 < (2 : ℝ) ^ n := by positivity
  have hnegPow (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ n)⁻¹ := by
    simp [zpow_neg, zpow_natCast]
  have hrecipLo : r⁻¹ ≤ ((2 : ℝ) ^ allocation_roundLength r)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hposPow _) hratioLo
  have hpowSucc : (2 : ℝ) ^ (allocation_roundLength r + 1) =
      2 * (2 : ℝ) ^ allocation_roundLength r := by
    rw [pow_succ]
    ring
  have hrecipHi : ((2 : ℝ) ^ (allocation_roundLength r + 1))⁻¹ < r⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt (by positivity) hratioHi
  have hscaleRecip : ((2 : ℝ) ^ allocation_roundLength r)⁻¹ =
      2 * ((2 : ℝ) ^ (allocation_roundLength r + 1))⁻¹ := by
    rw [hpowSucc]
    field_simp
  constructor
  · simpa [hnegPow] using hrecipLo
  · rw [hnegPow, hscaleRecip]
    exact mul_lt_mul_of_pos_left hrecipHi (by norm_num)

theorem allocation_list_sum_toFinset {α : Type*} [DecidableEq α] {β : Type*}
    [AddCommMonoid β] (f : α → β) (l : List α) (hl : l.Nodup) :
    ∑ x ∈ l.toFinset, f x = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rcases List.nodup_cons.mp hl with ⟨haNot, hl⟩
      have h := congrArg (fun z : β => f a + z) (ih hl)
      simpa [List.toFinset_cons, haNot, List.map_cons, List.sum_cons] using h

theorem allocation_list_natCast_sum {α : Type*} (f : α → ℕ) (l : List α) :
    ((l.map f).sum : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map_cons, List.sum_cons, ih]

end HypercubeRamsey.S13
