import HypercubeRamsey.S17.Needs
import HypercubeRamsey.S12

namespace HypercubeRamsey.Lane_q_s17_pool

open Classical
open Filter
open scoped BigOperators

theorem pi_expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (f : ∀ i, Ω i → ℝ) :
    (FinLaw.pi P).E (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (P i).E (f i) := by
  classical
  let g : ∀ i, Ω i → ℝ := fun i x => (P i).w x * f i x
  have hsum : (∑ ω : (∀ i, Ω i), ∏ i, g i (ω i)) =
      ∏ i, ∑ x : Ω i, g i x := by
    rw [← Fintype.prod_sum]
  calc
    (∑ ω : (∀ i, Ω i), (∏ i, (P i).w (ω i)) * (∏ i, f i (ω i))) =
        ∑ ω : (∀ i, Ω i), ∏ i, g i (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      simp [g, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ x : Ω i, (P i).w x * f i x := by
      simpa [g] using hsum
    _ = ∏ i, (∑ x : Ω i, (P i).w x * f i x) := rfl

theorem pi_expect_sum_prod {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (c : α → ℝ)
    (f : α → ∀ i, Ω i → ℝ) :
    (FinLaw.pi P).E (fun ω => ∑ a, c a * ∏ i, f a i (ω i)) =
      ∑ a, c a * ∏ i, (P i).E (f a i) := by
  classical
  change (∑ ω : (∀ i, Ω i), (∏ i, (P i).w (ω i)) *
      (∑ a, c a * ∏ i, f a i (ω i))) =
    ∑ a, c a * ∏ i, ∑ y : Ω i, (P i).w y * f a i y
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  let g : ∀ i, Ω i → ℝ := fun i y => (P i).w y * f a i y
  have hsum : (∑ ω : (∀ i, Ω i), ∏ i, g i (ω i)) =
      ∏ i, ∑ y : Ω i, g i y := by
    rw [← Fintype.prod_sum]
  calc
    (∑ ω : (∀ i, Ω i), (∏ i, (P i).w (ω i)) *
        (c a * ∏ i, f a i (ω i))) =
      c a * ∑ ω : (∀ i, Ω i), ∏ i, g i (ω i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω hω
        calc
          (∏ i, (P i).w (ω i)) * (c a * ∏ i, f a i (ω i)) =
              c a * ((∏ i, (P i).w (ω i)) * ∏ i, f a i (ω i)) := by ring
          _ = c a * ∏ i, g i (ω i) := by
            congr 1
            rw [← Finset.prod_mul_distrib]
    _ = c a * ∏ i, ∑ y : Ω i, (P i).w y * f a i y := by
      simpa [g] using congrArg (fun z : ℝ => c a * z) hsum
    _ = c a * ∏ i, (∑ y : Ω i, (P i).w y * f a i y) := rfl

theorem pinned_product_row_expectation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (pins : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k)) :
    (D.pinnedLabelLaw v pins fixed).E
        (fun ys => ∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
          D.hitRatio w.1 x (ys w)) =
      ∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
        (if w.1 ∈ pins then FinLaw.dirac (fixed w.1)
         else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))).E
          (fun y => D.hitRatio w.1 x y) := by
  classical
  let P : ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, FinLaw (Fin (T.S.N k)) :=
    fun w => if w.1 ∈ pins then FinLaw.dirac (fixed w.1)
      else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))
  let f : Fin (T.S.N k) →
      ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (T.S.N k) → ℝ :=
    fun x w y => D.hitRatio w.1 x y
  simpa [P, f, ListGateContext.pinnedLabelLaw] using
    (pi_expect_sum_prod P σ f)

theorem law_hitRatio_expectation {N : ℕ} (μ : Law N)
    (E : Fin N → Fin N → Prop) (c : Colour) (x : Fin N)
    (hdeg : 0 < deg E c μ.w x) :
    (ListGateContext.lawAsFinLaw μ).E
      (fun y => hit E c x y / deg E c μ.w x) = 1 := by
  classical
  change (∑ y, μ.w y * (hit E c x y / deg E c μ.w x)) = 1
  calc
    (∑ y, μ.w y * (hit E c x y / deg E c μ.w x)) =
        ∑ y, (μ.w y * hit E c x y) / deg E c μ.w x := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = (∑ y, μ.w y * hit E c x y) / deg E c μ.w x := by
          rw [Finset.sum_div]
    _ = 1 := by
          rw [show (∑ y, μ.w y * hit E c x y) = deg E c μ.w x by rfl]
          exact div_self (ne_of_gt hdeg)

noncomputable def reweightLaw {N : ℕ} (μ : Law N) (f : Fin N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ) (hZ : 0 < Z)
    (hZeq : ∑ x, μ.w x * f x = Z) : Law N where
  w x := μ.w x * f x / Z
  nonneg x := div_nonneg (mul_nonneg (μ.nonneg x) (hf x)) hZ.le
  sum_eq_one := by
    rw [← Finset.sum_div, hZeq, div_self hZ.ne']

theorem reweightLaw_atom_bound {N : ℕ} (μ : Law N) (f : Fin N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ) (hZ : 0 < Z)
    (hZeq : ∑ x, μ.w x * f x = Z)
    (w C : ℝ) (hμw : μ.WidthLE w) (hC : 0 ≤ C)
    (hfC : ∀ x, μ.w x ≠ 0 → f x ≤ C) (x : Fin N) :
    (reweightLaw μ f hf Z hZ hZeq).w x ≤ (C / Z) * Real.exp w / N := by
  by_cases hμ0 : μ.w x = 0
  · simp [reweightLaw, hμ0]
    positivity
  · have hprod : μ.w x * f x ≤ (Real.exp w / N) * C :=
      mul_le_mul (hμw x) (hfC x hμ0) (hf x) (by positivity)
    calc
      (reweightLaw μ f hf Z hZ hZeq).w x = μ.w x * f x / Z := rfl
      _ ≤ ((Real.exp w / N) * C) / Z := div_le_div_of_nonneg_right hprod hZ.le
      _ = (C / Z) * Real.exp w / N := by ring

theorem hitRatio_average_lower {N : ℕ} (μ : Law N)
    (E : Fin N → Fin N → Prop) (c : Colour) (y : Fin N)
    (d : Fin N → ℝ) (dmax : ℝ)
    (hdpos : ∀ x, μ.w x ≠ 0 → 0 < d x)
    (hdle : ∀ x, μ.w x ≠ 0 → d x ≤ dmax) :
    (∑ x, μ.w x * (hit E c x y / d x)) ≥
      (∑ x, μ.w x * hit E c x y) / dmax := by
  classical
  have hterm (x : Fin N) :
      μ.w x * (hit E c x y / dmax) ≤ μ.w x * (hit E c x y / d x) := by
    by_cases hμ0 : μ.w x = 0
    · simp [hμ0]
    · have hratio : hit E c x y / dmax ≤ hit E c x y / d x := by
        by_cases hhit : Hits E c x y
        · simp [hit, hhit]
          simpa [one_div] using
            (one_div_le_one_div_of_le (hdpos x hμ0) (hdle x hμ0))
        · simp [hit, hhit]
      exact mul_le_mul_of_nonneg_left hratio (μ.nonneg x)
  calc
    (∑ x, μ.w x * (hit E c x y / d x)) ≥
        ∑ x, μ.w x * (hit E c x y / dmax) := Finset.sum_le_sum fun x _ => hterm x
    _ = (∑ x, μ.w x * hit E c x y) / dmax := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem hitRatio_reweight_width_bound {N : ℕ} (μ : Law N)
    (E : Fin N → Fin N → Prop) (c : Colour) (y : Fin N)
    (d : Fin N → ℝ) (dmin dmax m w : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hm : 0 < m)
    (hμw : μ.WidthLE w)
    (hdpos : ∀ x, μ.w x ≠ 0 → 0 < d x)
    (hdmin' : ∀ x, μ.w x ≠ 0 → dmin ≤ d x)
    (hdmax' : ∀ x, μ.w x ≠ 0 → d x ≤ dmax)
    (hdegree : m ≤ ∑ x, μ.w x * hit E c x y) :
    ∃ ν : Law N, ∀ x,
      ν.w x ≤ (dmax / (m * dmin)) * Real.exp w / N := by
  classical
  let f : Fin N → ℝ := fun x => if 0 < d x then hit E c x y / d x else 0
  let Z : ℝ := ∑ x, μ.w x * f x
  have hf : ∀ x, 0 ≤ f x := by
    intro x
    dsimp [f]
    split_ifs with hd
    · apply div_nonneg
      · unfold hit
        split_ifs <;> norm_num
      · exact hd.le
    · exact le_rfl
  have hZeqRatio : Z = ∑ x, μ.w x * (hit E c x y / d x) := by
    dsimp [Z]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hμ0 : μ.w x = 0
    · simp [f, hμ0]
    · simp [f, hdpos x hμ0]
  have hZlower : m / dmax ≤ Z := by
    calc
      m / dmax ≤ (∑ x, μ.w x * hit E c x y) / dmax :=
        div_le_div_of_nonneg_right hdegree hdmax.le
      _ ≤ Z := by rw [hZeqRatio]; exact hitRatio_average_lower μ E c y d dmax hdpos hdmax'
  have hZpos : 0 < Z := lt_of_lt_of_le (div_pos hm hdmax) hZlower
  have hfC : ∀ x, μ.w x ≠ 0 → f x ≤ 1 / dmin := by
    intro x hx
    have hdxPos := hdpos x hx
    have hdxMin := hdmin' x hx
    by_cases hxy : Hits E c x y
    · simp [f, hit, hdxPos, hxy]
      simpa [one_div] using one_div_le_one_div_of_le hdmin hdxMin
    · simp [f, hit, hdxPos, hxy]
      exact le_of_lt hdmin
  have hZeq : ∑ x, μ.w x * f x = Z := rfl
  let ν : Law N := reweightLaw μ f hf Z hZpos hZeq
  have hrecip : 1 / Z ≤ dmax / m := by
    have h := one_div_le_one_div_of_le (div_pos hm hdmax) hZlower
    calc
      1 / Z ≤ 1 / (m / dmax) := h
      _ = dmax / m := by field_simp
  have hscale : (1 / dmin) / Z ≤ dmax / (m * dmin) := by
    calc
      (1 / dmin) / Z = (1 / dmin) * (1 / Z) := by ring
      _ ≤ (1 / dmin) * (dmax / m) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = dmax / (m * dmin) := by field_simp
  refine ⟨ν, ?_⟩
  intro x
  have hatom := reweightLaw_atom_bound μ f hf Z hZpos hZeq w (1 / dmin)
    hμw (by positivity) hfC x
  dsimp [ν]
  calc
    (reweightLaw μ f hf Z hZpos hZeq).w x ≤ ((1 / dmin) / Z) * Real.exp w / N := hatom
    _ ≤ (dmax / (m * dmin)) * Real.exp w / N := by
      gcongr

theorem pinned_product_row_expectation_simplified {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (pins : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k))
    (hdeg : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v,
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) :
    (D.pinnedLabelLaw v pins fixed).E
        (fun ys => ∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
          D.hitRatio w.1 x (ys w)) =
      ∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
        if w.1 ∈ pins then
          D.hitRatio w.1 x (fixed w.1) else 1 := by
  classical
  rw [pinned_product_row_expectation]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hσ : σ x = 0
  · simp [hσ]
  · congr 1
    apply Finset.prod_congr rfl
    intro w hw
    by_cases hp : w.1 ∈ pins
    · simp [hp, FinLaw.dirac, FinLaw.E]
    · have hratio := law_hitRatio_expectation
        (PT.π (D.G.patchOf w.1)) (T.S.E k) PT.tiling.c x
        (hdeg x hσ w.1 w.2)
      simpa [hp, ListGateContext.lawAsFinLaw, ListGateContext.hitRatio] using hratio

theorem pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (A : ∀ i, Ω i → Prop) :
    (FinLaw.pi P).pr (fun ω => ∀ i, A i (ω i)) =
      ∏ i, (P i).pr (A i) := by
  classical
  let f : ∀ i, Ω i → ℝ := fun i x => if A i x then (P i).w x else 0
  have hpoint : ∀ ω : (∀ i, Ω i),
      (if (∀ i, A i (ω i)) then ∏ i, (P i).w (ω i) else 0) =
      ∏ i, f i (ω i) := by
    intro ω
    by_cases h : ∀ i, A i (ω i)
    · simp [f, h]
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      have hnot : ¬ (∀ i, A i (ω i)) := by
        intro hall
        exact hi (hall i)
      have hzero : ∏ i, f i (ω i) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [f, hi]
      simp [f, hnot, hzero]
  calc
    (FinLaw.pi P).pr (fun ω => ∀ i, A i (ω i)) =
        ∑ ω : (∀ i, Ω i), ∏ i, f i (ω i) := by
      unfold FinLaw.pr FinLaw.pi
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : ∀ i, A i (ω i)
      · simpa [h] using hpoint ω
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        have hnot : ¬ (∀ i, A i (ω i)) := by
          intro hall
          exact hi (hall i)
        have hzero : ∏ i, f i (ω i) = 0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [f, hi]
        simpa [hnot, hzero] using hpoint ω
    _ = ∏ i, ∑ x, f i x := by rw [← Fintype.prod_sum]
    _ = ∏ i, (P i).pr (A i) := by simp [f, FinLaw.pr]

theorem pr_nonneg {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ μ.pr A := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs <;> simp [μ.nonneg]

theorem pi_pr_forall_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (A : ∀ i, Ω i → Prop) (q : ι → ℝ)
    (hq : ∀ i, (P i).pr (A i) ≤ q i) :
    (FinLaw.pi P).pr (fun ω => ∀ i, A i (ω i)) ≤ ∏ i, q i := by
  rw [pi_pr_forall]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact pr_nonneg (P i) (A i)
  · intro i hi
    exact hq i

theorem pr_mono {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω)
    {A B : Ω → Prop} (hAB : ∀ ω, A ω → B ω) :
    μ.pr A ≤ μ.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω
    · simp [hA, hB, μ.nonneg ω]
    · simp [hA, hB]

theorem pr_exists_finset_le {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] (μ : FinLaw Ω) (S : Finset ι) (A : ι → Ω → Prop) :
    μ.pr (fun ω => ∃ i ∈ S, A i ω) ≤ ∑ i ∈ S, μ.pr (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [FinLaw.pr]
  | @insert i S hi ih =>
      have hcover : ∀ ω, (∃ j ∈ insert i S, A j ω) →
          A i ω ∨ ∃ j ∈ S, A j ω := by
        intro ω ⟨j, hj, hA⟩
        rcases Finset.mem_insert.mp hj with rfl | hjS
        · exact Or.inl hA
        · exact Or.inr ⟨j, hjS, hA⟩
      calc
        μ.pr (fun ω => ∃ j ∈ insert i S, A j ω) ≤
            μ.pr (fun ω => A i ω ∨ ∃ j ∈ S, A j ω) := pr_mono μ hcover
        _ ≤ μ.pr (A i) + μ.pr (fun ω => ∃ j ∈ S, A j ω) :=
          FinLaw.pr_or_le μ (A i) (fun ω => ∃ j ∈ S, A j ω)
        _ ≤ μ.pr (A i) + ∑ j ∈ S, μ.pr (A j) := by
          gcongr
        _ = ∑ j ∈ insert i S, μ.pr (A j) := by
          simp [Finset.sum_insert, hi]

theorem expect_card_eq_sum_pr {Ω β : Type*} [Fintype Ω] [Fintype β]
    (μ : FinLaw Ω) (A : β → Ω → Prop) :
    μ.E (fun ω => ((Finset.univ.filter fun b => A b ω).card : ℝ)) =
      ∑ b, μ.pr (A b) := by
  classical
  have hcard (ω : Ω) :
      ((Finset.univ.filter fun b => A b ω).card : ℝ) =
        ∑ b, if A b ω then (1 : ℝ) else 0 := by
    rw [← Finset.sum_boole (fun b => A b ω) Finset.univ]
  unfold FinLaw.E FinLaw.pr
  calc
    (∑ ω, μ.w ω * ((Finset.univ.filter fun b => A b ω).card : ℝ)) =
        ∑ ω, μ.w ω * (∑ b, if A b ω then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hcard]
    _ = ∑ ω, ∑ b, if A b ω then μ.w ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      split_ifs <;> simp [mul_comm]
    _ = ∑ b, ∑ ω, if A b ω then μ.w ω else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b, μ.pr (A b) := rfl

theorem pr_true {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω) :
    μ.pr (fun _ => True) = 1 := by
  classical
  unfold FinLaw.pr
  simpa using μ.sum_one

theorem pr_hits_eq_deg {N : ℕ} (μ : FinLaw (Fin N))
    (E : Fin N → Fin N → Prop) (c : Colour) (x : Fin N) :
    μ.pr (fun y => Hits E c x y) = deg E c μ.w x := by
  classical
  unfold FinLaw.pr deg hit
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : Hits E c x y <;> simp [h]

theorem lowGeom_syndrome_flip {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (v : Pos T k)
    (j : Fin (T.S.n k)) :
    G.syndrome (flipPos v j) = G.syndrome v + G.ids j := by
  classical
  have hterm : ∀ l,
      (if (flipPos v j) l = true then G.ids l else 0) =
        (if v l = true then G.ids l else 0) +
          (if l = j then G.ids j else 0) := by
    intro l
    ext q
    by_cases hlj : l = j
    · subst l
      by_cases hv : v j
      · simp [flipPos, hv, CharTwo.add_self_eq_zero]
      · simp [flipPos, hv]
    · simp [flipPos, hlj]
  calc
    G.syndrome (flipPos v j) =
        ∑ l, ((if v l = true then G.ids l else 0) +
          (if l = j then G.ids j else 0)) := by
      unfold LowGeom.syndrome
      apply Finset.sum_congr rfl
      intro l hl
      exact hterm l
    _ = (∑ l, if v l = true then G.ids l else 0) +
        ∑ l, if l = j then G.ids j else 0 := Finset.sum_add_distrib
    _ = G.syndrome v + G.ids j := by simp [LowGeom.syndrome]

theorem lowGeom_late_flip_injective {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT)
    (hids : Function.Injective G.ids) (v : Pos T k)
    {i j : Fin (T.S.n k)}
    (hi : (G.classOf (flipPos v i)).isSome)
    (hj : (G.classOf (flipPos v j)).isSome)
    (hclass : G.classOf (flipPos v i) = G.classOf (flipPos v j)) :
    i = j := by
  classical
  have classValue {z : Pos T k} {t : Fin G.r}
      (hc : G.classOf z = some t) : G.syndrome z = (G.classEnum t).1 := by
    have hcond : ¬ IsEvenRole z ∧ G.syndrome z ∈ G.Lsub := by
      by_contra hnot
      have hnone : G.classOf z = none := by
        simp [LowGeom.classOf, hnot]
      rw [hnone] at hc
      contradiction
    simp [LowGeom.classOf, hcond] at hc
    simpa using congrArg Subtype.val (congrArg G.classEnum hc)
  cases hci : G.classOf (flipPos v i) with
  | none => simp [hci] at hi
  | some ti =>
    cases hcj : G.classOf (flipPos v j) with
    | none => simp [hcj] at hj
    | some tj =>
      have hti : ti = tj := by
        have h := congrArg (fun o : Option (Fin G.r) => o.getD ti) hclass
        simpa [hci, hcj] using h
      have hs : G.syndrome (flipPos v i) = G.syndrome (flipPos v j) := by
        rw [classValue hci, hti, classValue hcj]
      rw [lowGeom_syndrome_flip G v i, lowGeom_syndrome_flip G v j] at hs
      exact hids (add_left_cancel hs)

theorem lowGeom_late_count_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT)
    (hids : Function.Injective G.ids) (v : Pos T k) :
    (Finset.univ.filter fun i : Fin (T.S.n k) =>
      (G.classOf (flipPos v i)).isSome).card ≤ G.r := by
  classical
  let L : Finset (Fin (T.S.n k)) :=
    Finset.univ.filter fun i => (G.classOf (flipPos v i)).isSome
  let f : {i : Fin (T.S.n k) // i ∈ L} → Fin G.r := fun i =>
    (G.classOf (flipPos v i.1)).get (Finset.mem_filter.mp i.2).2
  have hf : Function.Injective f := by
    intro a b hab
    have ha := (Finset.mem_filter.mp a.2).2
    have hb := (Finset.mem_filter.mp b.2).2
    cases hca : G.classOf (flipPos v a.1) with
    | none => simp [hca] at ha
    | some ta =>
      cases hcb : G.classOf (flipPos v b.1) with
      | none => simp [hcb] at hb
      | some tb =>
        have htab : ta = tb := by
          simpa [f, hca, hcb] using hab
        have hclass : G.classOf (flipPos v a.1) = G.classOf (flipPos v b.1) := by
          rw [hca, hcb, htab]
        apply Subtype.ext
        exact lowGeom_late_flip_injective G hids v
          (by simpa [hca] using ha) (by simpa [hcb] using hb) hclass
  have hcard := Fintype.card_le_of_injective f hf
  have hcard' : Fintype.card {i : Fin (T.S.n k) // i ∈ L} ≤ G.r := by
    simpa using hcard
  have hL : L = Finset.univ.filter (fun i : Fin (T.S.n k) =>
      (G.classOf (flipPos v i)).isSome = true) := by
    ext i
    simp [L]
  rw [← hL]
  exact (Fintype.card_coe L).symm.trans_le hcard'

theorem tiling_internal_coord_card {κ : CConsts} {T : Stage} {k : ℕ}
    (𝒯 : Tiling κ T k) (i : Fin 𝒯.m)
    (hh : (𝒯.P i).h ≤ T.S.n k) :
    (𝒯.Icoord i).card = (𝒯.P i).h := by
  classical
  let n := T.S.n k
  let h := (𝒯.P i).h
  have hprefix : (Finset.univ.filter fun j : Fin n => j.val < n - h).card = n - h := by
    rw [Fin.card_filter_val_lt]
    simp [n, h, Nat.min_eq_right (Nat.sub_le _ _)]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun j => j.val < n - h)
  have hpartition' :
      (Finset.univ.filter fun j : Fin n => j.val < n - h).card +
        (Finset.univ.filter fun j : Fin n => n - h ≤ j.val).card = n := by
    simpa [Finset.card_univ, not_lt] using hpartition
  have hpartition'' := hpartition'
  rw [hprefix] at hpartition''
  have htop : (Finset.univ.filter fun j : Fin n => n - h ≤ j.val).card = h := by
    omega
  simpa [Tiling.Icoord, topCoordinates, n, h] using htop

theorem fin_prefix_coord_card {n ell : ℕ} (hell : ell ≤ n) :
    (Finset.univ.filter fun j : Fin n => j.val < ell).card = ell := by
  rw [Fin.card_filter_val_lt]
  simp [Nat.min_eq_right hell]

theorem lowGeom_patch_flip_of_after_prefix {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (G : LowGeom PT) (hPT : PT.Valid)
    (v : Pos T k) (j : Fin (T.S.n k))
    (hj : (PT.tiling.P (G.patchOf v)).ℓ ≤ j.val) :
    G.patchOf (flipPos v j) = G.patchOf v := by
  classical
  let i := G.patchOf v
  have hj' : (PT.tiling.P i).ℓ ≤ j.val := by simpa [i] using hj
  have hv : ∀ l : Fin (T.S.n k), l.val < (PT.tiling.P i).ℓ →
      v l = PT.tiling.w i l := by
    simpa [i, Tiling.leaf, prefixLeaf] using G.patchOf_leaf v
  have hflip : flipPos v j ∈ PT.tiling.leaf i := by
    intro l hl
    have hvl := hv l hl
    have hlj : l ≠ j := by
      intro h
      subst l
      omega
    simpa [flipPos, hlj] using hvl
  obtain ⟨i₀, hi₀, huniq⟩ := hPT.tiling_valid.prefix_complete (flipPos v j)
  have h1 : i = i₀ := huniq i hflip
  have h2 : G.patchOf (flipPos v j) = i₀ :=
    huniq (G.patchOf (flipPos v j)) (G.patchOf_leaf (flipPos v j))
  exact h2.trans h1.symm

theorem lowGeom_bulk_early_candidates {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hPT : PT.Valid) (hids : Function.Injective D.G.ids) (v : Pos T k) :
    ∃ B : Finset (Pos T k),
      B ⊆ D.externalEarly v ∧
      (∀ w ∈ B, D.G.patchOf w = D.G.patchOf v) ∧
      T.S.n k - ((PT.tiling.P (D.G.patchOf v)).h +
        (PT.tiling.P (D.G.patchOf v)).ℓ + D.G.r) ≤ B.card ∧
      B.card ≤ T.S.n k ∧
      (D.externalEarly v \ B).card ≤ (PT.tiling.P (D.G.patchOf v)).ℓ := by
  classical
  let i := D.G.patchOf v
  let n := T.S.n k
  let h := (PT.tiling.P i).h
  let ell := (PT.tiling.P i).ℓ
  let I : Finset (Fin n) := PT.tiling.Icoord i
  let Late : Finset (Fin n) :=
    Finset.univ.filter fun j => (D.G.classOf (flipPos v j)).isSome
  let Prefix : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell
  let bad : Finset (Fin n) := I ∪ Late ∪ Prefix
  let C : Finset (Fin n) := Finset.univ \ bad
  let B : Finset (Pos T k) := C.image (flipPos v)
  have hlength := hPT.tiling_valid.prefix_internal_length
  have hsupH : h ≤ Finset.univ.sup fun q : Fin PT.tiling.m => (PT.tiling.P q).h := by
    dsimp [h, i]
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin PT.tiling.m)))
      (f := fun q => (PT.tiling.P q).h) (Finset.mem_univ (D.G.patchOf v))
  have hsupEll : ell ≤ Finset.univ.sup fun q : Fin PT.tiling.m => (PT.tiling.P q).ℓ := by
    dsimp [ell, i]
    exact Finset.le_sup (s := (Finset.univ : Finset (Fin PT.tiling.m)))
      (f := fun q => (PT.tiling.P q).ℓ) (Finset.mem_univ (D.G.patchOf v))
  have hh : h ≤ n := by dsimp [n]; omega
  have hell : ell ≤ n := by dsimp [n]; omega
  have hIcard : I.card = h := by
    dsimp [I]
    exact tiling_internal_coord_card PT.tiling i hh
  have hLatecard : Late.card ≤ D.G.r := by
    dsimp [Late]
    exact lowGeom_late_count_le D.G hids v
  have hPrefixcard : Prefix.card = ell := by
    dsimp [Prefix, n]
    exact fin_prefix_coord_card hell
  have hbadcard : bad.card ≤ h + D.G.r + ell := by
    dsimp [bad]
    calc
      (I ∪ Late ∪ Prefix).card ≤ (I ∪ Late).card + Prefix.card :=
        Finset.card_union_le (I ∪ Late) Prefix
      _ ≤ (I.card + Late.card) + Prefix.card := by
        have hIL : (I ∪ Late).card ≤ I.card + Late.card :=
          Finset.card_union_le I Late
        gcongr
      _ ≤ h + D.G.r + ell := by omega
  have hCcard : C.card = n - bad.card := by
    dsimp [C]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ bad), Finset.card_univ]
    simp [n]
  have hClower : n - (h + D.G.r + ell) ≤ C.card := by
    rw [hCcard]
    omega
  have hflip : Function.Injective (flipPos v) := by
    intro a b hab
    by_contra hne
    have heq := congrArg (fun z : Pos T k => z a) hab
    have hleft : flipPos v a a = !v a := by simp [flipPos]
    have hright : flipPos v b a = v a := by simp [flipPos, hne]
    rw [hleft, hright] at heq
    cases hv : v a <;> simp [hv] at heq
  have hBcard : B.card = C.card := by
    dsimp [B]
    exact Finset.card_image_of_injective _ hflip
  have hgood : ∀ j, j ∈ C →
      j ∉ I ∧ D.G.classOf (flipPos v j) = none ∧
        D.G.patchOf (flipPos v j) = i := by
    intro j hj
    have hnotBad : j ∉ bad := (Finset.mem_sdiff.mp hj).2
    have hnotI : j ∉ I := by
      intro hmem
      exact hnotBad (by simp [bad, hmem])
    have hnotLate : j ∉ Late := by
      intro hmem
      exact hnotBad (by simp [bad, hmem])
    have hnotPrefix : j ∉ Prefix := by
      intro hmem
      exact hnotBad (by simp [bad, hmem])
    have hclass : D.G.classOf (flipPos v j) = none := by
      cases hc : D.G.classOf (flipPos v j) with
      | none => rfl
      | some t =>
        exfalso
        exact hnotLate (by simp [Late, hc])
    have hge : ell ≤ j.val := Nat.le_of_not_gt (by
      intro hlt
      exact hnotPrefix (by simp [Prefix, hlt]))
    have hpatch := lowGeom_patch_flip_of_after_prefix D.G hPT v j (by
      simpa [i, ell] using hge)
    exact ⟨hnotI, hclass, by simpa [i] using hpatch⟩
  have hcross_sub : D.externalEarly v \ B ⊆ Prefix.image (flipPos v) := by
    intro w hw
    have hwext := (Finset.mem_sdiff.mp hw).1
    have hwnotB := (Finset.mem_sdiff.mp hw).2
    rcases (Finset.mem_filter.mp hwext).2 with ⟨hclassw, ⟨j, hjI, hEq⟩⟩
    have hjnotPrefix : j ∈ Prefix := by
      by_contra hjnot
      have hclass : D.G.classOf (flipPos v j) = none := by
        rw [← hEq]
        exact hclassw
      have hjnotLate : j ∉ Late := by
        intro hjLate
        simp [Late, hclass] at hjLate
      have hjnotBad : j ∉ bad := by
        intro hjBad
        simp only [bad, Finset.mem_union] at hjBad
        rcases hjBad with hjIL | hjPrefix
        · rcases hjIL with hjI' | hjLate
          · exact hjI hjI'
          · exact hjnotLate hjLate
        · exact hjnot hjPrefix
      have hjgood : j ∈ C := by
        simp [C, hjnotBad]
      have hwB : flipPos v j ∈ B := Finset.mem_image.mpr ⟨j, hjgood, rfl⟩
      have hwnotB' : flipPos v j ∉ B := by simpa [hEq] using hwnotB
      exact hwnotB' hwB
    exact Finset.mem_image.mpr ⟨j, hjnotPrefix, hEq.symm⟩
  have hcross_card : (D.externalEarly v \ B).card ≤ ell := by
    calc
      (D.externalEarly v \ B).card ≤ (Prefix.image (flipPos v)).card :=
        Finset.card_le_card hcross_sub
      _ = Prefix.card := Finset.card_image_of_injective _ hflip
      _ = ell := hPrefixcard
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    have hg := hgood j hj
    simp only [ListGateContext.externalEarly, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨hg.2.1, ⟨j, by simpa [i] using hg.1, rfl⟩⟩
  · intro w hw
    rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
    exact (hgood j hj).2.2
  · change n - (h + ell + D.G.r) ≤ B.card
    calc
      n - (h + ell + D.G.r) = n - (h + D.G.r + ell) := by congr 1 <;> omega
      _ ≤ C.card := hClower
      _ = B.card := hBcard.symm
  · rw [hBcard]
    simpa [n] using Finset.card_le_univ C
  · simpa [ell] using hcross_card

theorem profiled_law_width_of_mass_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (K : ℝ)
    (hMass : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤
      K * Real.sqrt (Real.log (T.S.n k : ℝ))) :
    (PT.π i).WidthLE
      (K * Real.sqrt (Real.log (T.S.n k : ℝ)) + Real.log 11) := by
  classical
  intro y
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hMnat : 0 < (PT.tiling.P i).M := by
    rw [← (PT.tiling.P i).cardX]
    exact_mod_cast (Finset.card_pos.mpr (hPT.tiling_valid.patch_nonempty i).1)
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by exact_mod_cast hMnat
  have hratio : 0 < (T.S.N k : ℝ) / (PT.tiling.P i).M := div_pos hN hM
  have hidentity : (11 : ℝ) / (PT.tiling.P i).M =
      Real.exp (Real.log 11 + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) /
        (T.S.N k : ℝ) := by
    rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hratio]
    field_simp
  calc
    (PT.π i).w y ≤ 11 / (PT.tiling.P i).M := hPT.law_cap i y
    _ = Real.exp (Real.log 11 + Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M)) /
        (T.S.N k : ℝ) := hidentity
    _ ≤ Real.exp (Real.log 11 + K * Real.sqrt (Real.log (T.S.n k : ℝ))) /
        (T.S.N k : ℝ) := by
      apply div_le_div_of_nonneg_right ?_ hN.le
      exact Real.exp_le_exp.mpr (by nlinarith [hMass])
    _ = Real.exp (K * Real.sqrt (Real.log (T.S.n k : ℝ)) + Real.log 11) /
        (T.S.N k : ℝ) := by rw [add_comm]

theorem profiled_degree_tail {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {wS wL err : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL err)
    (hPT : PT.Valid) (i j : Fin PT.tiling.m) (τ : Law (T.S.N k))
    (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE wS)
    (W : ℝ) (hπw : (PT.π j).WidthLE W)
    : ∑ y ∈ Finset.univ.filter (fun y => err <
      |(∑ x, τ.w x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2|),
      (PT.π j).w y ≤ 2 * Real.exp (W - wL) := by
  have hYS : (PT.tiling.P j).Y ⊆ T.Y k := by
    intro y hy
    exact (Finset.mem_sdiff.mp
      ((hPT.tiling_valid.patch_supports j).2.2.2
        ((hPT.tiling_valid.patch_supports j).2.2.1 hy))).1
  have hπY : (PT.π j).SupportedIn (T.Y k) := by
    intro y hy
    exact hPT.law_supported j y (fun hmem => hy (hYS hmem))
  have hpair : (wS ≤ wS ∧ wL ≤ wL) ∨ (wS ≤ wL ∧ wL ≤ wS) :=
    Or.inl ⟨le_rfl, le_rfl⟩
  exact S12.exceptional_second (hD := hDisc) (c := PT.tiling.c)
    (w₁ := wS) (W₂ := wL) (w := W) hpair τ hτ hτw
    (PT.π j) hπY hπw

theorem product_filter_pins_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (pins : Finset (Pos T k))
    (hPins : pins ⊆ D.externalEarly v) (f : Pos T k → ℝ) :
    (∏ w : {w : Pos T k // w ∈ D.externalEarly v},
      if w.1 ∈ pins then f w.1 else 1) = ∏ w ∈ pins, f w := by
  classical
  let Ext := {w : Pos T k // w ∈ D.externalEarly v}
  let PinExt := {w : Ext // w.1 ∈ pins}
  let Pin := {w : Pos T k // w ∈ pins}
  let e : PinExt ≃ Pin := {
    toFun := fun w => ⟨w.1.1, w.2⟩
    invFun := fun w => ⟨⟨w.1, hPins w.2⟩, w.2⟩
    left_inv := by intro w; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro w; apply Subtype.ext; rfl }
  let p : Ext → Prop := fun w => w.1 ∈ pins
  let g : Ext → ℝ := fun w => if p w then f w.1 else 1
  have hPinG : (∏ w : PinExt, g w.1) = ∏ w : PinExt, f w.1.1 := by
    apply Fintype.prod_congr
    intro w
    simp [g, p, w.2]
  have hUnpinG : (∏ w : {w : Ext // ¬ p w}, g w.1) = 1 := by
    calc
      (∏ w : {w : Ext // ¬ p w}, g w.1) =
          ∏ w : {w : Ext // ¬ p w}, (1 : ℝ) := by
        apply Fintype.prod_congr
        intro w
        simp [g, p, w.2]
      _ = 1 := by simp
  have hpart := Fintype.prod_subtype_mul_prod_subtype p g
  rw [hUnpinG, mul_one] at hpart
  calc
    (∏ w : Ext, if w.1 ∈ pins then f w.1 else 1) =
        ∏ w : Ext, g w := by simp [g, p]
    _ = ∏ w : PinExt, f w.1.1 := hpart.symm.trans hPinG
    _ = ∏ w : Pin, f w.1 := Fintype.prod_equiv e _ _ (by intro w; rfl)
    _ = ∏ w ∈ pins, f w := Finset.prod_attach pins f

theorem pinnedPriorMass_eq_hits {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (hPT : PT.Valid)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (hσ : D.CleanInitialPrior v σ) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k)) :
    D.pinnedPriorMass v σ pins fixed =
      ∑ x, σ x * ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w) := by
  classical
  rcases hσ.2.2 with ⟨a, ha, hsupport, _, _⟩
  unfold ListGateContext.pinnedPriorMass
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hzero : σ x = 0
  · simp [hzero]
  · have hxclean : x ∈ PT.mesh.corner a (D.G.patchOf v) := hsupport x hzero
    have hxX : x ∈ (PT.tiling.P (D.G.patchOf v)).X :=
      (hPT.corner_clean (D.G.patchOf v) a ha).sub hxclean
    simp [hxX]

theorem cleanSupport_subset_envelope {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hPT : PT.Valid) (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (hσ : D.CleanInitialPrior v σ) (x : Fin (T.S.N k)) (hxσ : σ x ≠ 0) :
    x ∈ PT.envelope (D.G.patchOf v) := by
  classical
  rcases hσ.2.2 with ⟨a, ha, hsupport, _, _⟩
  rw [hPT.envelope_eq]
  exact Finset.mem_biUnion.mpr ⟨a, ha, hsupport x hxσ⟩

theorem cleanSupport_external_degree_drift {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hPT : PT.Valid) (K : ℝ) (hGeom : D.S17GeometryValidity K)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (hN : 0 < (T.S.n k : ℝ))
    (x : Fin (T.S.N k)) (hxσ : σ x ≠ 0) (w : Pos T k)
    (hw : w ∈ D.externalEarly v) :
    |deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x - 1 / 2| ≤
      max (K * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) (3 * bstar T k) := by
  let i := D.G.patchOf v
  let j := D.G.patchOf w
  have hxenv : x ∈ PT.envelope i := by
    simpa [i] using cleanSupport_subset_envelope D hPT v σ hσ x hxσ
  by_cases hji : j = i
  · have hpatch : D.G.patchOf w = D.G.patchOf v := by simpa [j, i] using hji
    have h := hGeom.degree_drift i x hxenv
    have hdiv : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤
        K * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ) :=
      (le_div_iff₀ hN).2 (by nlinarith [h])
    simpa [hpatch] using le_trans hdiv (le_max_left _ _)
  · have h := hPT.envelope_other_degree i j hji x hxenv
    simpa [j] using le_trans h (le_max_right _ _)

theorem cleanSupport_external_degree_bounds {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hPT : PT.Valid) (K : ℝ) (hGeom : D.S17GeometryValidity K)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (hN : 0 < (T.S.n k : ℝ)) (hδ :
      max (K * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) (3 * bstar T k) < 1 / 2)
    (x : Fin (T.S.N k)) (hxσ : σ x ≠ 0) (w : Pos T k)
    (hw : w ∈ D.externalEarly v) :
    0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ∧
    deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤
      1 / 2 + max (K * Real.log (T.S.n k : ℝ) / (T.S.n k : ℝ)) (3 * bstar T k) := by
  have h := cleanSupport_external_degree_drift D hPT K hGeom v σ hσ hN x hxσ w hw
  have hbound := abs_le.mp h
  constructor <;> linarith

theorem not_compatiblePool_iff {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (pools : D.PoolAssignment) :
    ¬ D.compatiblePool v pools ↔
      ∃ pins : Finset (Pos T k), pins ⊆ D.externalEarly v ∧
        pins.card ≤ ListGateContext.pinBudget κ ∧
        ∃ fixed : Pos T k → Fin (T.S.N k),
          (∀ w ∈ pins, fixed w ∈ D.permittedLabels (D.G.cellOf w) (pools (D.G.cellOf w)) w) ∧
          Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) <
            (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr
              (fun s => D.pinnedStatePriorMass v s pins fixed <
                (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ))) := by
  classical
  unfold ListGateContext.compatiblePool
  push_neg
  rfl

theorem rowMass_subtype_product {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (hN : 0 < T.S.N k) (σ : Fin (T.S.N k) → ℝ)
    (ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :
    D.rowMass v σ (D.labelsOfPinnedSample v hN ys) =
      ∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
        D.hitRatio w.1 x (ys w) := by
  classical
  unfold ListGateContext.rowMass ListGateContext.row
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  rw [← Finset.prod_attach, ← Finset.univ_eq_attach]
  apply Fintype.prod_congr
  intro w
  simp [ListGateContext.labelsOfPinnedSample]

theorem pinned_row_expectation_lower {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hPT : PT.Valid) (v : Pos T k) (σ : Fin (T.S.N k) → ℝ)
    (hσ : D.CleanInitialPrior v σ) (pins : Finset (Pos T k))
    (hPins : pins ⊆ D.externalEarly v) (fixed : Pos T k → Fin (T.S.N k))
    (dmax : ℝ) (hdmax : 0 < dmax)
    (hdeg : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v,
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ∧
      deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤ dmax) :
    (D.pinnedLabelLaw v pins fixed).E
        (fun ys => D.rowMass v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≥
      D.pinnedPriorMass v σ pins fixed / dmax ^ pins.card := by
  classical
  have hdegreePositive : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v,
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
    intro x hx w hw
    exact (hdeg x hx w hw).1
  have hExpectation :
      (D.pinnedLabelLaw v pins fixed).E
        (fun ys => D.rowMass v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) =
      ∑ x, σ x * ∏ w ∈ pins,
        hit (T.S.E k) PT.tiling.c x (fixed w) /
          deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
    calc
      (D.pinnedLabelLaw v pins fixed).E
          (fun ys => D.rowMass v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) =
          (D.pinnedLabelLaw v pins fixed).E (fun ys =>
            ∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
              D.hitRatio w.1 x (ys w)) := by
          unfold FinLaw.E
          apply Finset.sum_congr rfl
          intro ys hys
          change (D.pinnedLabelLaw v pins fixed).w ys *
              D.rowMass v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys) =
            (D.pinnedLabelLaw v pins fixed).w ys *
              (∑ x, σ x * ∏ w : {w : Pos T k // w ∈ D.externalEarly v},
                D.hitRatio w.1 x (ys w))
          congr 1
          exact rowMass_subtype_product D v (T.S.N_pos k) σ ys
      _ = ∑ x, σ x * ∏ w ∈ pins,
            hit (T.S.E k) PT.tiling.c x (fixed w) /
              deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
        rw [pinned_product_row_expectation_simplified D v σ pins fixed hdegreePositive]
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        rw [product_filter_pins_eq D v pins hPins
          (fun w => D.hitRatio w x (fixed w))]
        simp [ListGateContext.hitRatio]
  have hsum :
      (∑ x, σ x * ∏ w ∈ pins,
        hit (T.S.E k) PT.tiling.c x (fixed w) /
          deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) ≥
      (∑ x, σ x * ∏ w ∈ pins,
        hit (T.S.E k) PT.tiling.c x (fixed w)) / dmax ^ pins.card := by
    have hterm (x : Fin (T.S.N k)) :
        (σ x * ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)) /
          dmax ^ pins.card ≤ σ x * (∏ w ∈ pins,
          hit (T.S.E k) PT.tiling.c x (fixed w) /
            deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) := by
      by_cases hzero : σ x = 0
      · simp [hzero]
      · have hprod :
            (∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w) / dmax) ≤
            ∏ w ∈ pins,
              hit (T.S.E k) PT.tiling.c x (fixed w) /
                deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
          apply Finset.prod_le_prod₀
          · intro w hw
            unfold hit
            split_ifs <;> positivity
          · intro w hw
            have hden := hdeg x hzero w (hPins hw)
            by_cases hh : Hits (T.S.E k) PT.tiling.c x (fixed w)
            · simp [hit, hh]
              simpa [one_div] using one_div_le_one_div_of_le hden.1 hden.2
            · simp [hit, hh]
        have hproddiv :
            (∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w) / dmax) =
              (∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)) /
                dmax ^ pins.card := by
          rw [Finset.prod_div_distrib]
          simp
        calc
          (σ x * ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)) /
              dmax ^ pins.card =
              σ x * (∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w) / dmax) := by
                rw [hproddiv]
                ring
          _ ≤ σ x * (∏ w ∈ pins,
              hit (T.S.E k) PT.tiling.c x (fixed w) /
                deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) :=
            mul_le_mul_of_nonneg_left hprod (hσ.1 x)
    calc
      (∑ x, σ x * ∏ w ∈ pins,
          hit (T.S.E k) PT.tiling.c x (fixed w) /
            deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x) ≥
          ∑ x, (σ x * ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)) /
            dmax ^ pins.card := Finset.sum_le_sum fun x _ => hterm x
      _ = (∑ x, σ x * ∏ w ∈ pins, hit (T.S.E k) PT.tiling.c x (fixed w)) /
            dmax ^ pins.card := by rw [Finset.sum_div]
  calc
    (D.pinnedLabelLaw v pins fixed).E
        (fun ys => D.rowMass v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) =
        ∑ x, σ x * ∏ w ∈ pins,
          hit (T.S.E k) PT.tiling.c x (fixed w) /
            deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := hExpectation
    _ ≥ D.pinnedPriorMass v σ pins fixed / dmax ^ pins.card := by
      simpa only [pinnedPriorMass_eq_hits D hPT v σ hσ pins fixed] using hsum

theorem externalEarly_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) : (D.externalEarly v).card ≤ T.S.n k := by
  classical
  have hflip : Function.Injective (flipPos v) := by
    intro a b hab
    by_contra hne
    have heq := congrArg (fun z : Pos T k => z a) hab
    have hleft : flipPos v a a = !v a := by simp [flipPos]
    have hright : flipPos v b a = v a := by simp [flipPos, hne]
    rw [hleft, hright] at heq
    cases hv : v a <;> simp [hv] at heq
  have hsub : D.externalEarly v ⊆
      Finset.univ.image (flipPos v) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨_, ⟨_, ⟨j, hj, rfl⟩⟩⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  calc
    (D.externalEarly v).card ≤ (Finset.univ.image (flipPos v)).card :=
      Finset.card_le_card hsub
    _ = (Finset.univ : Finset (Fin (T.S.n k))).card :=
      Finset.card_image_of_injective _ hflip
    _ = T.S.n k := by simp

theorem pinned_support_point_probability {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (hN : 0 < T.S.N k)
    (pins J B : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k))
    (hBext : B ⊆ D.externalEarly v)
    (hBpatch : ∀ w ∈ B, D.G.patchOf w = D.G.patchOf v)
    (hBavoid : ∀ w ∈ B, w ∉ pins ∧ w ∉ J)
    (x : Fin (T.S.N k)) (a : ℝ)
    (hdegree : deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x ≤ a) :
    (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => x ∈ D.omittedList v J
        (D.labelsOfPinnedSample v hN ys)) ≤ a ^ B.card := by
  classical
  let Index := {w : Pos T k // w ∈ D.externalEarly v}
  let embed : {w : Pos T k // w ∈ B} → Index := fun w =>
    ⟨w.1, hBext w.2⟩
  let selected : Finset Index := B.attach.image embed
  let laws : ∀ w : Index, FinLaw (Fin (T.S.N k)) := fun w =>
    if w.1 ∈ pins then FinLaw.dirac (fixed w.1)
    else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))
  let event : Index → Fin (T.S.N k) → Prop := fun w y =>
    w ∈ selected → Hits (T.S.E k) PT.tiling.c x y
  let q : Index → ℝ := fun w => if w ∈ selected then a else 1
  have hembed : Function.Injective embed := by
    intro w z hwz
    apply Subtype.ext
    exact congrArg (fun t : Index => t.1) hwz
  have hScard : selected.card = B.card := by
    dsimp [selected]
    rw [Finset.card_image_of_injective _ hembed]
    simp
  have hselected_iff (w : Index) : w ∈ selected ↔ w.1 ∈ B := by
    constructor
    · intro hw
      rcases Finset.mem_image.mp hw with ⟨w', hw', heq⟩
      have hwB : w'.1 ∈ B := w'.2
      have hval : w'.1 = w.1 := congrArg (fun t : Index => t.1) heq
      exact hval ▸ hwB
    · intro hwB
      refine Finset.mem_image.mpr ⟨⟨w.1, hwB⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      rfl
  have hcoord : ∀ w : Index, (laws w).pr (event w) ≤ q w := by
    intro w
    by_cases hw : w ∈ selected
    · have hwB := (hselected_iff w).mp hw
      have hnotPin := (hBavoid w.1 hwB).1
      have hpatch := hBpatch w.1 hwB
      have hlaw : laws w = ListGateContext.lawAsFinLaw
          (PT.π (D.G.patchOf v)) := by
        dsimp [laws]
        simp [hnotPin, hpatch]
      have hevent : event w = fun y => Hits (T.S.E k) PT.tiling.c x y := by
        funext y
        simp [event, hw]
      rw [hevent, hlaw]
      calc
        (ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf v))).pr
            (fun y => Hits (T.S.E k) PT.tiling.c x y) =
            deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x :=
          pr_hits_eq_deg _ _ _ _
        _ ≤ a := hdegree
        _ = q w := by simp [q, hw]
    · have hevent : event w = fun _ => True := by
        funext y
        simp [event, hw]
      rw [hevent]
      simp [q, hw, pr_true]
  let μ := D.pinnedLabelLaw v pins fixed
  have hμ : μ = FinLaw.pi laws := rfl
  have hsubset : ∀ ys, x ∈ D.omittedList v J
      (D.labelsOfPinnedSample v hN ys) → ∀ w : Index, event w (ys w) := by
    intro ys hbad w
    by_cases hw : w ∈ selected
    · intro _
      have hwB := (hselected_iff w).mp hw
      have hwJ := (hBavoid w.1 hwB).2
      rcases Finset.mem_filter.mp hbad with ⟨_, ⟨_, hhits⟩⟩
      have hhit := hhits w.1 (Finset.mem_sdiff.mpr ⟨w.2, hwJ⟩)
      have hlabel : D.labelsOfPinnedSample v hN ys w.1 = ys w := by
        simp [ListGateContext.labelsOfPinnedSample, w.2]
      simpa [event, hw, hlabel] using hhit
    · intro h
      exact False.elim (hw h)
  have hprod : ∏ w : Index, q w = a ^ selected.card := by
    simp [q, Finset.prod_ite_mem]
  calc
    μ.pr (fun ys => x ∈ D.omittedList v J
        (D.labelsOfPinnedSample v hN ys)) ≤
        μ.pr (fun ys => ∀ w : Index, event w (ys w)) :=
      pr_mono μ hsubset
    _ = (FinLaw.pi laws).pr (fun ys => ∀ w : Index, event w (ys w)) := by rw [hμ]
    _ ≤ ∏ w : Index, q w := pi_pr_forall_le laws event q hcoord
    _ = a ^ B.card := by rw [hprod, hScard]

theorem pinned_support_expected_card_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (hN : 0 < T.S.N k)
    (pins J B : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k))
    (hBext : B ⊆ D.externalEarly v)
    (hBpatch : ∀ w ∈ B, D.G.patchOf w = D.G.patchOf v)
    (hBavoid : ∀ w ∈ B, w ∉ pins ∧ w ∉ J)
    (a : ℝ) (ha : 0 ≤ a)
    (hdegree : ∀ x ∈ PT.envelope (D.G.patchOf v),
      deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x ≤ a) :
    (D.pinnedLabelLaw v pins fixed).E
      (fun ys => (D.omittedList v J
        (D.labelsOfPinnedSample v hN ys)).card) ≤
      (T.S.N k : ℝ) * a ^ B.card := by
  classical
  let μ := D.pinnedLabelLaw v pins fixed
  have hpoint (x : Fin (T.S.N k)) :
      μ.pr (fun ys => x ∈ D.omittedList v J
        (D.labelsOfPinnedSample v hN ys)) ≤ a ^ B.card := by
    by_cases hx : x ∈ PT.envelope (D.G.patchOf v)
    · exact pinned_support_point_probability D v hN pins J B fixed hBext hBpatch
        hBavoid x a (hdegree x hx)
    · have hempty : ∀ ys, x ∉ D.omittedList v J
          (D.labelsOfPinnedSample v hN ys) := by
        intro ys hmem
        unfold ListGateContext.omittedList at hmem
        have hx' := (Finset.mem_filter.mp hmem).2.1
        exact hx hx'
      have hzero : μ.pr (fun ys =>
          x ∈ D.omittedList v J (D.labelsOfPinnedSample v hN ys)) = 0 := by
        unfold FinLaw.pr
        apply Finset.sum_eq_zero
        intro ys hys
        simp [hempty ys]
      rw [hzero]
      exact pow_nonneg ha _
  calc
    μ.E (fun ys => (D.omittedList v J
        (D.labelsOfPinnedSample v hN ys)).card) =
        ∑ x, μ.pr (fun ys => x ∈ D.omittedList v J
          (D.labelsOfPinnedSample v hN ys)) :=
      by
        simpa [ListGateContext.omittedList] using
          expect_card_eq_sum_pr μ (fun x ys => x ∈ D.omittedList v J
            (D.labelsOfPinnedSample v hN ys))
    _ ≤ ∑ x, a ^ B.card := by
      apply Finset.sum_le_sum
      intro x hx
      exact hpoint x
    _ = (T.S.N k : ℝ) * a ^ B.card := by simp [Finset.sum_const, nsmul_eq_mul]

theorem pr_markov {Ω : Type*} [Fintype Ω] (μ : FinLaw Ω)
    (f : Ω → ℝ) (t : ℝ) (hf : ∀ ω, 0 ≤ f ω) (ht : 0 < t) :
    μ.pr (fun ω => t ≤ f ω) ≤ μ.E f / t := by
  classical
  let A : Ω → Prop := fun ω => t ≤ f ω
  have hpoint : t * μ.pr A ≤ μ.E f := by
    unfold FinLaw.pr FinLaw.E
    rw [Finset.mul_sum]
    calc
      (∑ ω, t * (if A ω then μ.w ω else 0)) =
          ∑ ω, μ.w ω * (if A ω then t else 0) := by
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hA : A ω <;> simp [hA, mul_comm]
      _ ≤ ∑ ω, μ.w ω * f ω := by
        apply Finset.sum_le_sum
        intro ω hω
        by_cases hA : A ω
        · have htf : t ≤ f ω := hA
          simpa [hA] using mul_le_mul_of_nonneg_left htf (μ.nonneg ω)
        · simpa [hA] using mul_nonneg (μ.nonneg ω) (hf ω)
  apply (le_div_iff₀ ht).2
  calc
    μ.pr A * t = t * μ.pr A := by ring
    _ ≤ μ.E f := hpoint

theorem neg_rpow_le_eighth {x e : ℝ} (hx : 2 ≤ x) (he : 3 ≤ e) :
    Real.rpow x (-e) ≤ (1 / 8 : ℝ) := by
  have hx1 : 1 ≤ x := by linarith
  have h1 : Real.rpow x (-e) ≤ Real.rpow x (-3) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h2 : Real.rpow x (-3) ≤ Real.rpow 2 (-3) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by norm_num)
  calc
    Real.rpow x (-e) ≤ Real.rpow x (-3) := h1
    _ ≤ Real.rpow 2 (-3) := h2
    _ = 1 / 8 := by norm_num

theorem pool_tail_numeric {x R P : ℝ} {m : ℕ}
    (hx : 2 ≤ x) (hm₁ : 3 ≤ R * (m : ℝ) / 2)
    (hm₂ : 3 ≤ (R / 2 - P) * (m : ℝ)) :
    2 * Real.rpow x (-(R * (m : ℝ))) +
      2 * Real.rpow x (-((R - P) * (m : ℝ))) ≤
      Real.rpow x (-(R * (m : ℝ) / 2)) := by
  have hsmall₁ := neg_rpow_le_eighth hx hm₁
  have hsmall₂ := neg_rpow_le_eighth hx hm₂
  let a := Real.rpow x (-(R * (m : ℝ) / 2))
  have ha : 0 ≤ a := Real.rpow_nonneg (by linarith) _
  have hfirst : Real.rpow x (-(R * (m : ℝ))) = a * a := by
    calc
      Real.rpow x (-(R * (m : ℝ))) =
          Real.rpow x (-(R * (m : ℝ) / 2) + -(R * (m : ℝ) / 2)) := by
        congr 1 <;> ring
      _ = Real.rpow x (-(R * (m : ℝ) / 2)) *
          Real.rpow x (-(R * (m : ℝ) / 2)) :=
        Real.rpow_add (by linarith [hx]) _ _
      _ = a * a := by rfl
  have hsecond : Real.rpow x (-((R - P) * (m : ℝ))) =
      a * Real.rpow x (-((R / 2 - P) * (m : ℝ))) := by
    calc
      Real.rpow x (-((R - P) * (m : ℝ))) =
          Real.rpow x (-(R * (m : ℝ) / 2) + -((R / 2 - P) * (m : ℝ))) := by
        congr 1 <;> ring
      _ = Real.rpow x (-(R * (m : ℝ) / 2)) *
          Real.rpow x (-((R / 2 - P) * (m : ℝ))) :=
        Real.rpow_add (by linarith [hx]) _ _
      _ = a * Real.rpow x (-((R / 2 - P) * (m : ℝ))) := by rfl
  have hfirstSmall : 2 * Real.rpow x (-(R * (m : ℝ))) ≤ a / 4 := by
    rw [hfirst]
    have hmul := mul_le_mul_of_nonneg_left hsmall₁ ha
    nlinarith
  have hsecondSmall :
      2 * Real.rpow x (-((R - P) * (m : ℝ))) ≤ a / 4 := by
    rw [hsecond]
    have hmul := mul_le_mul_of_nonneg_left hsmall₂ ha
    nlinarith
  change 2 * Real.rpow x (-(R * (m : ℝ))) +
      2 * Real.rpow x (-((R - P) * (m : ℝ))) ≤ a
  linarith

theorem rpow_quotient {x R P : ℝ} {m : ℕ} (hx : 0 < x) :
    Real.rpow x (-(R * (m : ℝ))) /
        (Real.rpow x (-P)) ^ m =
      Real.rpow x (-((R - P) * (m : ℝ))) := by
  have hbase : 0 < Real.rpow x (-P) := Real.rpow_pos_of_pos hx _
  have hden : 0 < (Real.rpow x (-P)) ^ m := pow_pos hbase _
  have hpow : (Real.rpow x (-P)) ^ m =
      Real.rpow x (-P * (m : ℝ)) := by
    calc
      (Real.rpow x (-P)) ^ m = (Real.rpow x (-P)) ^ (m : ℝ) := by
        rw [Real.rpow_natCast]
      _ = Real.rpow x ((-P) * (m : ℝ)) :=
        (Real.rpow_mul (le_of_lt hx) (-P) (m : ℝ)).symm
  have hmul : Real.rpow x (-(R * (m : ℝ))) =
      Real.rpow x (-((R - P) * (m : ℝ))) *
        (Real.rpow x (-P)) ^ m := by
    rw [hpow]
    calc
      Real.rpow x (-(R * (m : ℝ))) =
          Real.rpow x (-((R - P) * (m : ℝ)) + (-P * (m : ℝ))) := by
        congr 1 <;> ring
      _ = Real.rpow x (-((R - P) * (m : ℝ))) *
          Real.rpow x (-P * (m : ℝ)) := Real.rpow_add hx _ _
  rw [hmul, mul_div_cancel_right₀ _ (ne_of_gt hden)]

theorem support_union_numerical_bound {n N m d loss : ℕ} {K C R y : ℝ}
    (hn : 0 < (n : ℝ)) (hy : 1 ≤ y) (hlog : Real.log (n : ℝ) = y)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hKC : K ≤ C)
    (hsmall : C * y ^ 4 ≤ (n : ℝ) / 4)
    (hN : N ≤ n * 2 ^ n) (hmle : m ≤ n) (hmloss : n - m ≤ loss)
    (hLoss : (loss : ℝ) ≤ C * y ^ 4) (hd : (d : ℝ) ≤ y ^ 4)
    (hR : 0 ≤ R) (hY : C + 3 + 2 * K + 2 * R ≤ y) :
    ((n : ℝ) ^ d * (N : ℝ) * (1 / 2 + K * y / n) ^ m) /
        Real.exp (y ^ 8) ≤
      (1 / 2 : ℝ) * Real.rpow (n : ℝ) (-2 * R) := by
  have hy2 : y ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hy4' : y ^ 2 ≤ y ^ 4 := by nlinarith [sq_nonneg (y ^ 2 - 1)]
  have hy4 : y ≤ y ^ 4 := hy2.trans hy4'
  have hKy : K * y ≤ C * y ^ 4 := by
    calc
      K * y ≤ K * y ^ 4 := mul_le_mul_of_nonneg_left hy4 hK
      _ ≤ C * y ^ 4 := mul_le_mul_of_nonneg_right hKC (by positivity)
  have hKyDiv : K * y / (n : ℝ) ≤ 1 / 4 :=
    (div_le_iff₀ hn).2 (by linarith [hKy, hsmall])
  let a : ℝ := 1 / 2 + K * y / n
  let u : ℝ := 2 * K * y / n
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; linarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsumExp : (1 + u) ^ m ≤ Real.exp (u * (m : ℝ)) := by
    have h := Real.prod_one_add_le_exp_sum (Finset.univ : Finset (Fin m))
      (f := fun _ => u) (fun _ => hu)
    simpa [Finset.prod_const, Finset.sum_const, nsmul_eq_mul, mul_comm] using h
  have hform : a = (1 / 2 : ℝ) * (1 + u) := by
    dsimp [a, u]
    ring
  have hmreal : (m : ℝ) ≤ n := by exact_mod_cast hmle
  have huMul : u * (m : ℝ) ≤ 2 * K * y := by
    dsimp [u]
    calc
      (2 * K * y / (n : ℝ)) * (m : ℝ) =
          (2 * K * y) * ((m : ℝ) / n) := by ring
      _ ≤ (2 * K * y) * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one₀ hn).2 hmreal) (by positivity)
      _ = 2 * K * y := by ring
  have haPow : a ^ m ≤ (1 / 2 : ℝ) ^ m * Real.exp (2 * K * y) := by
    rw [hform, mul_pow]
    calc
      (1 / 2 : ℝ) ^ m * (1 + u) ^ m ≤
          (1 / 2 : ℝ) ^ m * Real.exp (u * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hsumExp (pow_nonneg (by norm_num) _)
      _ ≤ (1 / 2 : ℝ) ^ m * Real.exp (2 * K * y) := by
        gcongr
  have hmn : n = m + (n - m) := by omega
  have hpowCancel : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ m =
      (2 : ℝ) ^ (n - m) := by
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (m + (n - m)) :=
      congrArg (fun t : ℕ => (2 : ℝ) ^ t) hmn
    rw [hpow, pow_add]
    have hcancel : (2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      ((2 : ℝ) ^ m * (2 : ℝ) ^ (n - m)) * (1 / 2 : ℝ) ^ m =
          ((2 : ℝ) ^ m * (1 / 2 : ℝ) ^ m) * (2 : ℝ) ^ (n - m) := by ring
      _ = (2 : ℝ) ^ (n - m) := by rw [hcancel, one_mul]
  have h2exp : (2 : ℝ) ^ (n - m) ≤ Real.exp (loss : ℝ) := by
    have hp : (2 : ℝ) ^ (n - m) ≤ (2 : ℝ) ^ loss :=
      pow_le_pow_right₀ (by norm_num) hmloss
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hp' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he loss
    have hexp : (Real.exp 1) ^ loss = Real.exp (loss : ℝ) := by
      calc
        (Real.exp 1) ^ loss = Real.exp ((loss : ℝ) * 1) :=
          (Real.exp_nat_mul (1 : ℝ) loss).symm
        _ = Real.exp (loss : ℝ) := by rw [mul_one]
    exact hp.trans (hp'.trans_eq hexp)
  have hNcast : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by
    exact_mod_cast hN
  have hNpow : (N : ℝ) * a ^ m ≤
      Real.exp ((C + 1 + 2 * K) * y ^ 4) := by
    have hprod : (N : ℝ) * a ^ m ≤
        ((n : ℝ) * (2 : ℝ) ^ n) * ((1 / 2 : ℝ) ^ m * Real.exp (2 * K * y)) :=
      mul_le_mul hNcast haPow (pow_nonneg ha0 _) (by positivity)
    have hexpN : Real.exp y = (n : ℝ) := by
      rw [← hlog]
      exact Real.exp_log hn
    calc
      (N : ℝ) * a ^ m ≤
          ((n : ℝ) * (2 : ℝ) ^ n) * ((1 / 2 : ℝ) ^ m * Real.exp (2 * K * y)) := hprod
      _ = (n : ℝ) * ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ m) * Real.exp (2 * K * y) := by ring
      _ = (n : ℝ) * (2 : ℝ) ^ (n - m) * Real.exp (2 * K * y) := by rw [hpowCancel]
      _ ≤ (n : ℝ) * Real.exp (loss : ℝ) * Real.exp (2 * K * y) := by
        gcongr
      _ = Real.exp y * Real.exp (loss : ℝ) * Real.exp (2 * K * y) := by
        rw [← hexpN]
      _ = Real.exp (y + (loss : ℝ) + 2 * K * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((C + 1 + 2 * K) * y ^ 4) := by
        apply Real.exp_le_exp.mpr
        have hy14 : y ≤ y ^ 4 := hy4
        nlinarith [hLoss]
  have hnd : (n : ℝ) ^ d ≤ Real.exp (y ^ 5) := by
    have hexpN : Real.exp y = (n : ℝ) := by
      rw [← hlog]
      exact Real.exp_log hn
    have hdy : (d : ℝ) * y ≤ y ^ 5 := by
      calc
        (d : ℝ) * y ≤ y ^ 4 * y := mul_le_mul_of_nonneg_right hd (by linarith)
        _ = y ^ 5 := by ring
    calc
      (n : ℝ) ^ d = (Real.exp y) ^ d := by rw [hexpN]
      _ = Real.exp ((d : ℝ) * y) := (Real.exp_nat_mul y d).symm
      _ ≤ Real.exp (y ^ 5) := Real.exp_le_exp.mpr hdy
  let C₁ : ℝ := C + 1 + 2 * K
  let C₂ : ℝ := 1 + C₁
  have hprod : (n : ℝ) ^ d * (N : ℝ) * a ^ m ≤ Real.exp (C₂ * y ^ 5) := by
    calc
      (n : ℝ) ^ d * (N : ℝ) * a ^ m =
          (n : ℝ) ^ d * ((N : ℝ) * a ^ m) := by ring
      _ ≤ Real.exp (y ^ 5) * Real.exp (C₁ * y ^ 4) :=
        mul_le_mul hnd hNpow (by positivity) (by positivity)
      _ = Real.exp (y ^ 5 + C₁ * y ^ 4) := by rw [← Real.exp_add]
      _ ≤ Real.exp (C₂ * y ^ 5) := by
        apply Real.exp_le_exp.mpr
        have hy45 : y ^ 4 ≤ y ^ 5 := by
          calc
            y ^ 4 = y ^ 4 * 1 := by ring
            _ ≤ y ^ 4 * y := mul_le_mul_of_nonneg_left hy (by positivity)
            _ = y ^ 5 := by ring
        dsimp [C₁, C₂]
        nlinarith [hC, hK, hy, hy45]
  have hy2 : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hy3 : y ≤ y ^ 3 := by
    calc
      y = y * 1 := by ring
      _ ≤ y * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (by linarith)
      _ = y ^ 3 := by ring
  have hpolyCoeff : C₂ + 2 * R + 1 ≤ y ^ 3 := by
    dsimp [C₂, C₁]
    exact le_trans (by linarith [hY]) hy3
  have hpoly : C₂ * y ^ 5 + 2 * R * y + 1 ≤ y ^ 8 := by
    have hcoeff := mul_le_mul_of_nonneg_right hpolyCoeff (by positivity : 0 ≤ y ^ 5)
    have hy5y : y ≤ y ^ 5 := by
      calc
        y ≤ y ^ 3 := hy3
        _ = y ^ 3 * 1 := by ring
        _ ≤ y ^ 3 * y ^ 2 := mul_le_mul_of_nonneg_left hy2 (by positivity)
        _ = y ^ 5 := by ring
    have hy5one : 1 ≤ y ^ 5 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hy 5
    have hRterm : 2 * R * y ≤ 2 * R * y ^ 5 :=
      mul_le_mul_of_nonneg_left hy5y (by linarith [hR])
    have hsumR := add_le_add hRterm hy5one
    have hsum : C₂ * y ^ 5 + 2 * R * y + 1 ≤
        C₂ * y ^ 5 + (2 * R * y ^ 5 + y ^ 5) := by
      simpa [add_assoc] using
        add_le_add (le_rfl : C₂ * y ^ 5 ≤ C₂ * y ^ 5) hsumR
    calc
      C₂ * y ^ 5 + 2 * R * y + 1 ≤
          C₂ * y ^ 5 + (2 * R * y ^ 5 + y ^ 5) := hsum
      _ = (C₂ + 2 * R + 1) * y ^ 5 := by ring
      _ ≤ y ^ 3 * y ^ 5 := hcoeff
      _ = y ^ 8 := by ring
  have htail : Real.exp (C₂ * y ^ 5 - y ^ 8) ≤ Real.exp (-2 * R * y - 1) :=
    Real.exp_le_exp.mpr (by linarith [hpoly])
  have hratio : Real.rpow (n : ℝ) (-2 * R) = Real.exp (-2 * R * y) := by
    calc
      Real.rpow (n : ℝ) (-2 * R) =
          Real.exp (Real.log (n : ℝ) * (-2 * R)) :=
        Real.rpow_def_of_pos hn _
      _ = Real.exp (-2 * R * y) := by rw [hlog]; congr 1 <;> ring
  have hinv : Real.exp (-1 : ℝ) ≤ (1 / 2 : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc
      Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
      _ ≤ (2 : ℝ)⁻¹ := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).2 he
      _ = 1 / 2 := by norm_num
  have htarget : Real.exp (-2 * R * y - 1) ≤
      (1 / 2 : ℝ) * Real.rpow (n : ℝ) (-2 * R) := by
    rw [show -2 * R * y - 1 = (-1 : ℝ) + (-2 * R * y) by ring, Real.exp_add]
    calc
      Real.exp (-1 : ℝ) * Real.exp (-2 * R * y) ≤
          (1 / 2 : ℝ) * Real.exp (-2 * R * y) :=
        mul_le_mul_of_nonneg_right hinv (Real.exp_nonneg _)
      _ = (1 / 2 : ℝ) * Real.rpow (n : ℝ) (-2 * R) := by rw [← hratio]
  calc
    ((n : ℝ) ^ d * (N : ℝ) * a ^ m) / Real.exp (y ^ 8) ≤
        Real.exp (C₂ * y ^ 5) / Real.exp (y ^ 8) :=
      div_le_div_of_nonneg_right hprod (by positivity)
    _ = Real.exp (C₂ * y ^ 5 - y ^ 8) := by rw [← Real.exp_sub]
    _ ≤ Real.exp (-2 * R * y - 1) := htail
    _ ≤ (1 / 2 : ℝ) * Real.rpow (n : ℝ) (-2 * R) := htarget

theorem support_failure_from_union_bound {Ω α : Type*} [Fintype Ω] [Fintype α]
    (μ : FinLaw Ω) (Family : Finset α) (Bad : α → Ω → Prop) (S : Ω → Prop)
    (hcover : ∀ ω, S ω → ∃ a ∈ Family, Bad a ω)
    (ρ : ℝ) (hprob : ∀ a ∈ Family, μ.pr (Bad a) ≤ ρ) :
    μ.pr S ≤ (Family.card : ℝ) * ρ := by
  classical
  calc
    μ.pr S ≤ μ.pr (fun ω => ∃ a ∈ Family, Bad a ω) := pr_mono μ hcover
    _ ≤ ∑ a ∈ Family, μ.pr (Bad a) := pr_exists_finset_le μ Family Bad
    _ ≤ ∑ a ∈ Family, ρ := by
      apply Finset.sum_le_sum
      intro a ha
      exact hprob a ha
    _ = (Family.card : ℝ) * ρ := by simp [Finset.sum_const, nsmul_eq_mul]

theorem eventually_log4_small (T : Stage) (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ k in atTop,
      C * (Real.log (T.S.n k : ℝ)) ^ 4 ≤ (T.S.n k : ℝ) / 4 := by
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
      T.S.n_tendsto
  have hLittle : (fun x : ℝ => C * (Real.log x) ^ 4) =o[atTop] fun x => x :=
    (Real.isLittleO_pow_log_id_atTop (n := 4)).const_mul_left C
  have hEvent := hnT.eventually (hLittle.def (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hEvent, hnT.eventually_ge_atTop (1 : ℝ)] with k hk hn
  have hy : 0 ≤ Real.log (T.S.n k : ℝ) := Real.log_nonneg hn
  have hn0 : 0 ≤ (T.S.n k : ℝ) := by positivity
  calc
    C * (Real.log (T.S.n k : ℝ)) ^ 4 ≤
        (1 / 4 : ℝ) * (T.S.n k : ℝ) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hC, abs_of_nonneg hy,
        abs_of_nonneg hn0] using hk
    _ = (T.S.n k : ℝ) / 4 := by ring

end HypercubeRamsey.Lane_q_s17_pool
