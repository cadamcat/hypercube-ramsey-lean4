import HypercubeRamsey.S17.Nodes_sol_s17_pool_mass
import HypercubeRamsey.S17.Nodes_sol_s17_pool_experiment

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.Lane_sol_s17_pool

open Classical Filter
open scoped BigOperators

/-- A product experiment integrates a fixed coordinate partition in either order. -/
theorem pi_pr_partition {I α : Type*} [Fintype I] [Fintype α]
    [instI : DecidableEq I] (P : I → FinLaw α) (p : I → Prop)
    [instP : DecidablePred p] (A : (I → α) → Prop) :
    (FinLaw.pi P).pr A =
      (FinLaw.pi fun i : {i // p i} => P i.1).E (fun y =>
        (FinLaw.pi fun i : {i // ¬ p i} => P i.1).pr (fun z =>
          A (fun i => if h : p i then y ⟨i, h⟩ else z ⟨i, h⟩))) := by
  classical
  letI : DecidableEq I := instI
  letI : DecidablePred p := instP
  let e := Equiv.piEquivPiSubtypeProd p (fun _ : I => α)
  unfold FinLaw.pr FinLaw.E
  change (∑ s, if A s then ∏ i, (P i).w (s i) else 0) = _
  rw [← Fintype.sum_equiv e.symm _ _ (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hw : (∏ i, (P i).w ((e.symm (y, z)) i)) =
      (∏ i : {i // p i}, (P i.1).w (y i)) *
        ∏ i : {i // ¬ p i}, (P i.1).w (z i) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    congr 1 <;> apply Fintype.prod_congr <;> intro i <;> simp [e, i.2]
  rw [hw]
  change (if A _ then _ else 0) = _
  split_ifs <;> simp_all [e, Equiv.piEquivPiSubtypeProd, FinLaw.pi]

/-- Polynomially small drift in a fixed number of pinned denominators
retains seven eighths of the row. -/
theorem pinned_mass_seven_eighths (s s₀ : ℕ) (δ : ℝ)
    (hs : s ≤ s₀) (hδ : 0 ≤ δ) (hsmall : 2 * (s₀ : ℝ) * δ ≤ 1 / 100)
    (hδsmall : δ ≤ 1 / 4) :
    (7 / 8 : ℝ) ≤ ((9 / 10 : ℝ) * Real.rpow 2 (-(s : ℝ))) /
      (1 / 2 + δ) ^ s := by
  have hpos : 0 < (1 / 2 : ℝ) + δ := by linarith
  have hbase : 1 - 2 * δ ≤ (1 / 2 : ℝ) / (1 / 2 + δ) := by
    apply (le_div_iff₀ hpos).2
    nlinarith [sq_nonneg δ]
  have hBern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -2 * δ by linarith) s
  have hsr : (s : ℝ) ≤ (s₀ : ℝ) := by exact_mod_cast hs
  have hsδ := mul_le_mul_of_nonneg_right hsr hδ
  have hpow : (99 / 100 : ℝ) ≤ ((1 / 2 : ℝ) / (1 / 2 + δ)) ^ s := by
    calc
      _ ≤ 1 + (s : ℝ) * (-2 * δ) := by nlinarith
      _ ≤ (1 + (-2 * δ)) ^ s := hBern
      _ ≤ ((1 / 2 : ℝ) / (1 / 2 + δ)) ^ s := by
        apply pow_le_pow_left₀ (by linarith) (by linarith [hbase])
  have htwo : Real.rpow (2 : ℝ) (-(s : ℝ)) = (1 / 2 : ℝ) ^ s := by
    change (2 : ℝ) ^ (-(s : ℝ)) = _
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    simp [one_div, inv_pow]
  rw [htwo, mul_div_assoc, ← div_pow]
  nlinarith

/-- A short crossing sequence with the cleaned denominator window retains
fifteen sixteenths of its normalized starting mass. -/
theorem crossing_mass_fifteen_sixteenths (c : ℕ) (b err : ℝ)
    (hb : 0 ≤ b) (he : 0 ≤ err) (heb : err ≤ b)
    (hbsmall : b ≤ 1 / 16) (hc : 8 * (c : ℝ) * b ≤ 1 / 16) :
    (15 / 16 : ℝ) ≤ (((1 / 2 : ℝ) - err) / (1 / 2 + 3 * b)) ^ c := by
  have hp : 0 < (1 / 2 : ℝ) + 3 * b := by linarith
  have hbase : 1 - 8 * b ≤ ((1 / 2 : ℝ) - err) / (1 / 2 + 3 * b) := by
    apply (le_div_iff₀ hp).2
    nlinarith [sq_nonneg b]
  have hBern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -8 * b by linarith) c
  calc
    _ ≤ 1 + (c : ℝ) * (-8 * b) := by nlinarith
    _ ≤ (1 + (-8 * b)) ^ c := hBern
    _ ≤ _ := pow_le_pow_left₀ (by linarith) (by linarith [hbase]) c

/-- The positive direct-mode degree gain gives an exponential saving over
the baseline factor `2^d` when at least half the bulk incidences remain. -/
theorem direct_bulk_denominator_saving (n d : ℕ) (g D : ℝ)
    (hn : 0 < (n : ℝ)) (hg : 0 ≤ g) (hgn : g ≤ n)
    (hd : (n : ℝ) / 2 ≤ d) (hD : 1 / 2 + g / (4 * n) ≤ D) :
    Real.rpow D (-(d : ℝ)) ≤ (2 : ℝ) ^ d * Real.exp (-g / 16) := by
  have hp : 0 < D := by have := div_nonneg hg (show 0 ≤ 4 * (n : ℝ) by positivity); linarith
  have h2D : 1 ≤ 2 * D := by have := div_nonneg hg (show 0 ≤ 4 * (n : ℝ) by positivity); linarith
  have hbase : 1 + g / (2 * n) ≤ 2 * D := by
    convert mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hgp : 0 ≤ g / (2 * n) := by positivity
  have hg1 : g / (2 * n) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hlog : g / (4 * n) ≤ Real.log (2 * D) := by
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + g / (2 * n) by positivity)
    have hx : g / (2 * n) / 2 ≤ 1 - (1 + g / (2 * n))⁻¹ := by
      have hpos : 0 < 1 + g / (2 * n) := by positivity
      have heq : 1 - (1 + g / (2 * n))⁻¹ =
          (g / (2 * n)) / (1 + g / (2 * n)) := by
        field_simp
        ring
      rw [heq, le_div_iff₀ hpos]
      nlinarith
    have hm := Real.log_le_log (show 0 < 1 + g / (2 * n) by positivity) hbase
    calc
      g / (4 * n) = g / (2 * n) / 2 := by ring
      _ ≤ 1 - (1 + g / (2 * n))⁻¹ := hx
      _ ≤ Real.log (1 + g / (2 * n)) := h
      _ ≤ _ := hm
  have hsaving : g / 16 ≤ (d : ℝ) * Real.log (2 * D) := by
    have h₁ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d)
    have h₂ := mul_le_mul_of_nonneg_right hd (div_nonneg hg (show 0 ≤ 4 * (n : ℝ) by positivity))
    have heq : (n : ℝ) / 2 * (g / (4 * n)) = g / 8 := by field_simp <;> ring
    rw [heq] at h₂
    linarith
  have hlogD := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) hp.ne'
  change D ^ (-(d : ℝ)) ≤ _
  rw [Real.rpow_def_of_pos hp]
  have hexp : Real.exp ((d : ℝ) * Real.log 2) = (2 : ℝ) ^ d := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc
    _ ≤ Real.exp ((d : ℝ) * Real.log 2 - g / 16) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hlogD]
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, hexp]; congr 1; congr 1; ring

/-- Erasing deterministic coordinates from an independent experiment leaves
the product law on the remaining coordinates. -/
theorem pi_pr_erase_diracs {I α : Type*} [Fintype I] [Fintype α]
    [instI : DecidableEq I] (p : I → Prop) [instP : DecidablePred p]
    (fixed : I → α) (P : I → FinLaw α)
    (hP : ∀ i, p i → P i = FinLaw.dirac (fixed i))
    (A : (I → α) → Prop) :
    (FinLaw.pi P).pr A =
      (FinLaw.pi fun i : {i // ¬ p i} => P i.1).pr (fun z =>
        A (fun i => if h : p i then fixed i else z ⟨i, h⟩)) := by
  classical
  letI : DecidableEq I := instI
  letI : DecidablePred p := instP
  let fill : ({i // ¬ p i} → α) → I → α := fun z i =>
    if h : p i then fixed i else z ⟨i, h⟩
  let f : ({i // ¬ p i} → α) → ℝ := fun z => if A (fill z) then 1 else 0
  have hlocal : (FinLaw.pi P).pr A =
      (FinLaw.pi P).E (fun s => f (fun i => s i.1)) := by
    unfold FinLaw.pr FinLaw.E
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hw : (FinLaw.pi P).w s = 0
    · simp [hw]
    · have hfix : ∀ i, p i → s i = fixed i := by
        intro i hi
        by_contra hne
        have hfactor : (P i).w (s i) = 0 := by
          rw [hP i hi]
          simp [FinLaw.dirac, hne]
        have hz : (FinLaw.pi P).w s = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) hfactor
        exact hw hz
      have hfill : fill (fun i => s i.1) = s := by
        funext i
        dsimp [fill]
        split_ifs with hi
        · exact (hfix i hi).symm
        · rfl
      simp [f, hfill]
  rw [hlocal]
  have he := pi_E_injective_readouts P (fun i : {i // ¬ p i} => i.1)
    Subtype.val_injective (fun _ => id) f
  simp only [id_eq] at he
  rw [he]
  have hId : ∀ i : {i // ¬ p i}, FinLaw.map (P i.1) id = P i.1 := by
    intro i
    apply S16.Lane_q_s16_comp2.finLaw_ext
    intro a
    simp [FinLaw.map]
  simp_rw [hId]
  simp only [FinLaw.E, FinLaw.pr, f, fill, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr
  · ext z; simp
  · intro z hz
    split_ifs <;> simp only [FinLaw.pi]

/-- A law reindexed by a finite equivalence has the same product experiment. -/
theorem pi_pr_equiv {I J α : Type*} [Fintype I] [Fintype J] [Fintype α]
    [instI : DecidableEq I] [instJ : DecidableEq J] (e : I ≃ J)
    (P : J → FinLaw α) (A : (J → α) → Prop) :
    (FinLaw.pi P).pr A =
      (FinLaw.pi fun i => P (e i)).pr (fun z => A (fun j => z (e.symm j))) := by
  classical
  letI : DecidableEq I := instI
  letI : DecidableEq J := instJ
  let ee := Equiv.arrowCongr e (Equiv.refl α)
  unfold FinLaw.pr
  apply Fintype.sum_equiv ee.symm
  intro z
  have hfill : (fun j => (ee.symm z) (e.symm j)) = z := by
    funext j
    simp [ee]
  dsimp only
  simp only [hfill]
  split_ifs
  · change (∏ j, (P j).w (z j)) = ∏ i, (P (e i)).w ((ee.symm z) i)
    exact (Fintype.prod_equiv e _ _ (fun i => by simp [ee])).symm
  · rfl

/-- Erase the prescribed labels and factor their normalized row from the actual pinned experiment. -/
theorem pinned_row_failure_reduction {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (τ : Law (T.S.N k))
    (pins : Finset (Pos T k)) (hPins : pins ⊆ D.externalEarly v)
    (fixed : Pos T k → Fin (T.S.N k)) (Z : ℝ)
    (hrow : ∀ x, Z * τ.w x = σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w)) :
    (D.pinnedLabelLaw v pins fixed).pr (fun ys =>
      D.gateMassFailure v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) =
    (FinLaw.pi fun w : {w // w ∈ D.externalEarly v \ pins} =>
      ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))).pr (fun zs =>
        Z * (∑ x, τ.w x * ∏ w : {w // w ∈ D.externalEarly v \ pins},
          D.hitRatio w.1 x (zs w)) < 1 / 2) := by
  classical
  let I := {w : Pos T k // w ∈ D.externalEarly v}
  let U := {w : Pos T k // w ∈ D.externalEarly v \ pins}
  let p : I → Prop := fun w => w.1 ∈ pins
  let P : I → FinLaw (Fin (T.S.N k)) := fun w =>
    if w.1 ∈ pins then FinLaw.dirac (fixed w.1)
    else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))
  let A : (I → Fin (T.S.N k)) → Prop := fun ys =>
    D.gateMassFailure v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)
  have hErase := pi_pr_erase_diracs p (fun w => fixed w.1) P
    (fun w hw => by
      change w.1 ∈ pins at hw
      dsimp [P]
      rw [if_pos hw]
      apply S16.Lane_q_s16_comp2.finLaw_ext
      intro a
      simp [FinLaw.dirac]) A
  let e : U ≃ {w : I // ¬ p w} := {
    toFun := fun w => ⟨⟨w.1, (Finset.mem_sdiff.mp w.2).1⟩, (Finset.mem_sdiff.mp w.2).2⟩
    invFun := fun w => ⟨w.1.1, Finset.mem_sdiff.mpr ⟨w.1.2, w.2⟩⟩
    left_inv := fun w => rfl
    right_inv := fun w => rfl }
  have hEq := pi_pr_equiv e (fun w => P w.1) (fun zs =>
    A (fun w => if h : p w then fixed w.1 else zs ⟨w, h⟩))
  change (FinLaw.pi P).pr A = _
  have hAll : (FinLaw.pi P).pr A =
      (FinLaw.pi fun w : U => P (e w).1).pr (fun zs =>
        A (fun w => if h : p w then fixed w.1 else zs (e.symm ⟨w, h⟩))) := by
    convert hErase.trans hEq using 1 <;>
      unfold FinLaw.pr <;> apply Finset.sum_congr (by ext; simp) <;>
      intro zs hzs <;> split_ifs <;> simp only [FinLaw.pi]
  rw [hAll]
  have hP : (fun w : U => P (e w).1) =
      (fun w : U => ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))) := by
    funext w
    simp [P, e, (Finset.mem_sdiff.mp w.2).2]
  rw [hP]
  congr 1
  funext zs
  apply propext
  let ys : I → Fin (T.S.N k) := fun w =>
    if h : p w then fixed w.1 else zs (e.symm ⟨w, h⟩)
  let labels := D.labelsOfPinnedSample v (T.S.N_pos k) ys
  have hfixed : ∀ w ∈ pins, labels w = fixed w := by
    intro w hw
    simp [labels, ListGateContext.labelsOfPinnedSample, hPins hw, ys, p, hw]
  have hlabel : ∀ w : U, labels w.1 = zs w := by
    intro w
    have hext := (Finset.mem_sdiff.mp w.2).1
    have hnot := (Finset.mem_sdiff.mp w.2).2
    simp [labels, ListGateContext.labelsOfPinnedSample, hext, ys, p, hnot, e]
  have hmass : D.rowMass v σ labels =
      Z * (∑ x, τ.w x * ∏ w : U, D.hitRatio w.1 x (zs w)) := by
    rw [rowMass_after_pins D v σ τ pins hPins fixed labels Z hfixed hrow]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    rw [← Finset.prod_attach, ← Finset.univ_eq_attach]
    apply Fintype.prod_congr
    intro w
    rw [hlabel w]
  change D.rowMass v σ labels < 1 / 2 ↔ _
  rw [hmass]

/-- The extracted clique scale and the fine cluster degree drift are paid
for by the allocation gain, uniformly over low-mode patches. -/
theorem low_mode_gain_budgets {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m) :
    0 ≤ PT.tiling.gain i ∧
    (PT.tiling.mode ≠ .bounded →
      ((PT.tiling.P i).ℓ : ℝ) ≤ PT.tiling.gain i ∧
      Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ PT.tiling.gain i ∧
      Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ) ≤ PT.tiling.gain i) ∧
    (PT.tiling.mode = .lowCluster →
      40 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤ PT.tiling.gain i) := by
  have hu : (1 : ℝ) ≤ κ.u := by exact_mod_cast (by have := hκ.u_rng.2; omega : 1 ≤ κ.u)
  have ha : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hC : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
  have hG : 0 ≤ PT.tiling.gain i := by
    unfold Tiling.gain
    cases PT.tiling.mode <;> positivity
  refine ⟨hG, ?_, ?_⟩
  · intro hnot
    have halloc := (D.tiling_valid.tiling_valid.allocation_bounds i).2
    obtain ⟨hℓ, hmass⟩ := halloc.resolve_left hnot
    have hden : 0 < (1000 : ℝ) * κ.u := by positivity
    have hgainDiv : PT.tiling.gain i / (1000 * κ.u) ≤ PT.tiling.gain i :=
      (div_le_iff₀ hden).2 (by nlinarith)
    refine ⟨hℓ.trans hgainDiv, hmass.trans hgainDiv, ?_⟩
    cases hm : PT.tiling.mode with
    | bounded => exact False.elim (hnot hm)
    | lowDirect =>
      have hclique := (D.tiling_valid.tiling_valid.clique_scales i).2 (Or.inl hm)
      have hg : (0 : ℝ) ≤ (PT.tiling.P i).g := Nat.cast_nonneg _
      have hSQ : 0 < Real.sqrt κ.M1 := Real.sqrt_pos.2 (by linarith [hκ.M1_big.1])
      calc
        _ ≤ Cstar κ.u κ.ξ * (2 * (PT.tiling.P i).g / Real.sqrt κ.M1) :=
          mul_le_mul_of_nonneg_left hclique.2.2.1 hC
        _ = (2 * Cstar κ.u κ.ξ / Real.sqrt κ.M1) * (PT.tiling.P i).g := by ring
        _ ≤ (1e-4 : ℝ) * (PT.tiling.P i).g := mul_le_mul_of_nonneg_right hκ.M1_big.2 hg
        _ ≤ _ := by simp [Tiling.gain, hm]; linarith
    | lowCluster =>
      have hc := D.tiling_valid.tiling_valid.cluster_data (Or.inl hm) i
      have hqm : κ.M1 * κ.Q0 ≤ κ.M1 * (PT.tiling.P i).q :=
        hc.1.trans (by
        rw [Nat.cast_max]
        exact max_le hc.2.1 (by nlinarith [hκ.M1_big.1, (Nat.cast_nonneg (PT.tiling.P i).q : (0 : ℝ) ≤ (PT.tiling.P i).q)]))
      have hq0 : κ.Q0 ≤ ((PT.tiling.P i).q : ℝ) :=
        (mul_le_mul_iff_right₀ (show 0 < κ.M1 by linarith [hκ.M1_big.1])).mp hqm
      rcases hκ.Q0_large _ hq0 with ⟨_, _, _, _, _, _, hconf, _, _⟩
      have hh : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mlo ≤ (PT.tiling.P i).h := by
        simpa [hm] using hc.2.2.2.2.2.2.2.1
      have hGbound : 4 * Cstar κ.u κ.ξ * ((PT.tiling.P i).q : ℝ) ^ 2 ≤ PT.tiling.gain i := by
        have hhh := mul_le_mul_of_nonneg_left hh (show 0 ≤ κ.a / 10 ^ 6 by positivity)
        simp only [Tiling.gain, hm]
        nlinarith
      have hQ := (D.tiling_valid.tiling_valid.clique_scales i).1 (Or.inl hm)
      have hmult := mul_le_mul_of_nonneg_left hQ.2.2.1 hC
      nlinarith [hGbound]
    | highDirect => have := D.mode_low; simp [Mode.isLow, hm] at this
    | highSmall => have := D.mode_low; simp [Mode.isLow, hm] at this
    | highLarge => have := D.mode_low; simp [Mode.isLow, hm] at this
  · intro hm
    have hc := D.tiling_valid.tiling_valid.cluster_data (Or.inl hm) i
    have hqm : κ.M1 * κ.Q0 ≤ κ.M1 * (PT.tiling.P i).q :=
      hc.1.trans (by
        rw [Nat.cast_max]
        exact max_le hc.2.1 (by nlinarith [hκ.M1_big.1, (Nat.cast_nonneg (PT.tiling.P i).q : (0 : ℝ) ≤ (PT.tiling.P i).q)]))
    have hq0 : κ.Q0 ≤ ((PT.tiling.P i).q : ℝ) :=
      (mul_le_mul_iff_right₀ (show 0 < κ.M1 by linarith [hκ.M1_big.1])).mp hqm
    rcases hκ.Q0_large _ hq0 with ⟨_, _, _, _, _, _, _, hdrift, _⟩
    have hh : Real.rpow ((PT.tiling.P i).q : ℝ) κ.Mlo ≤ (PT.tiling.P i).h := by
      simpa [hm] using hc.2.2.2.2.2.2.2.1
    have hhh := mul_le_mul_of_nonneg_left hh (show 0 ≤ κ.a / 10 ^ 6 by positivity)
    have hden : 0 < (100 : ℝ) * κ.u := by positivity
    have hdiv := div_le_div_of_nonneg_right hhh hden.le
    have hgainDiv : PT.tiling.gain i / (100 * κ.u) ≤ PT.tiling.gain i :=
      (div_le_iff₀ hden).2 (by nlinarith)
    apply le_trans hdrift
    apply le_trans _ hgainDiv
    convert hdiv using 1 <;> simp only [Tiling.gain, hm] <;> ring

/-- The exact mode windows absorb clique, crossing and bulk drift costs.
The remaining factor is the binary incidence count used for late saving. -/
theorem low_mode_gamma_numerator {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (τ : Law (T.S.N k)) (s c d : ℕ)
    (hc : c ≤ (PT.tiling.P (D.G.patchOf v)).ℓ)
    (hd : d ≤ T.S.n k) (hdHalf : (T.S.n k : ℝ) / 2 ≤ d)
    (hn : 0 < (T.S.n k : ℝ)) (hbd : 4 * κ.Kbd ≤ T.S.n k)
    (hg : PT.tiling.mode = .lowDirect → ((PT.tiling.P (D.G.patchOf v)).g : ℝ) ≤ T.S.n k)
    (hgain : PT.tiling.gain (D.G.patchOf v) ≤ T.S.n k)
    (x : Fin (T.S.N k)) (hx : x ∈ PT.envelope (D.G.patchOf v))
    (hτ : τ.w x ≤ 2 * (4 : ℝ) ^ (s + c) * σ x) :
    (T.S.N k : ℝ) * (Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q (D.G.patchOf v) : ℝ)) *
      τ.w x * Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) (-(d : ℝ))) ≤
      (1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd)) *
        (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P (D.G.patchOf v)).h + d) := by
  classical
  let i := D.G.patchOf v
  let G := PT.tiling.gain i
  let D₀ := deg (T.S.E k) PT.tiling.c (PT.π i).w x
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  change c ≤ (PT.tiling.P i).ℓ at hc
  change PT.tiling.mode = .lowDirect → ((PT.tiling.P i).g : ℝ) ≤ T.S.n k at hg
  change G ≤ T.S.n k at hgain
  change (T.S.N k : ℝ) * (Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) *
      τ.w x * D₀ ^ (-(d : ℝ))) ≤
      (1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd)) *
        (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P i).h + d)
  have hτ0 := τ.nonneg x
  have hσ0 := hσ.1 x
  have hNτ0 := mul_nonneg hN.le hτ0
  have hD0 : 0 ≤ D₀ := Finset.sum_nonneg (fun y _ =>
    mul_nonneg ((PT.π i).nonneg y) (by unfold hit; split_ifs <;> norm_num))
  have hDPow : 0 ≤ D₀ ^ (-(d : ℝ)) := Real.rpow_nonneg hD0 _
  obtain ⟨hG, hbud, hcluDrift⟩ := low_mode_gain_budgets hκ D i
  have hC : 0 ≤ Cstar κ.u κ.ξ := by unfold Cstar; positivity
  have hKbd : 0 ≤ κ.Kbd := le_trans (by norm_num) hκ.bounded.2.2.2.1
  have hFixed : (1 : ℝ) ≤ Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd) :=
    Real.one_le_exp_iff.2 (by positivity)
  have hτN : (T.S.N k : ℝ) * τ.w x ≤ 2 * (4 : ℝ) ^ (s + c) * ((T.S.N k : ℝ) * σ x) := by
    convert mul_le_mul_of_nonneg_left hτ hN.le using 1 <;> ring
  have hpow2 : (2 : ℝ) ^ ((PT.tiling.P i).h + d) =
      (2 : ℝ) ^ (PT.tiling.P i).h * (2 : ℝ) ^ d := pow_add _ _ _
  have hOwn := D.tiling_valid.envelope_degree i x hx
  have hunbounded (hnot : PT.tiling.mode ≠ .bounded) :
      (4 : ℝ) ^ c ≤ Real.exp (3 * G) ∧
        Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) ≤ Real.exp G := by
    obtain ⟨hℓ, _, hQ⟩ := hbud hnot
    have hcR : (c : ℝ) ≤ G := (by exact_mod_cast hc : (c : ℝ) ≤ (PT.tiling.P i).ℓ).trans hℓ
    have hLog4 : Real.log (4 : ℝ) ≤ 3 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      norm_num at hh
      exact hh
    have hExp4 : Real.exp ((c : ℝ) * Real.log 4) = (4 : ℝ) ^ c := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    refine ⟨?_, Real.exp_le_exp.2 hQ⟩
    rw [← hExp4]
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hLog4 (Nat.cast_nonneg c)
    linarith
  cases hm : PT.tiling.mode with
  | bounded =>
    have hdata := D.tiling_valid.tiling_valid.bounded_data hm
    have hiData := hdata.2 i
    have hc0 : c = 0 := by have := hiData.1; omega
    have hh0 := hiData.2.1
    have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
      have hMnat := Finset.card_pos.mpr (D.tiling_valid.tiling_valid.patch_nonempty i).1
      rw [(PT.tiling.P i).cardX] at hMnat
      exact_mod_cast hMnat
    have hratio : (T.S.N k : ℝ) / (PT.tiling.P i).M ≤ 400 := by
      apply (div_le_iff₀ hM).2
      linarith [hiData.2.2.2.1]
    have hmass : Real.log ((T.S.N k : ℝ) / (PT.tiling.P i).M) ≤ Real.log 400 :=
      Real.log_le_log (div_pos hN hM) hratio
    have hcap := clean_prior_cap D v σ hσ (Real.log 400)
      (Real.log_nonneg (by norm_num)) hmass hG
    have hσN : (T.S.N k : ℝ) * σ x ≤ 800 := by
      have hh := hcap x
      change (T.S.N k : ℝ) * σ x ≤ 2 ^ (PT.tiling.P i).h * (2 * Real.exp (Real.log 400)) at hh
      rw [hh0, Real.exp_log (by norm_num : (0 : ℝ) < 400)] at hh
      norm_num at hh
      exact hh
    have hD : 1 / 2 - κ.Kbd / T.S.n k ≤ D₀ := by
      simp only [OwnDegOK, hm] at hOwn
      exact (by have := (abs_le.mp hOwn).1; dsimp [D₀, i]; linarith)
    have hden := bounded_bulk_denominator_cost (T.S.n k) d κ.Kbd D₀ hn hd hKbd hbd hD
    have hQeq := hiData.2.2.2.2
    change (T.S.N k : ℝ) * (Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) * τ.w x * D₀ ^ (-(d : ℝ))) ≤ _
    calc
      _ = Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) *
          ((T.S.N k : ℝ) * τ.w x) * D₀ ^ (-(d : ℝ)) := by ring
      _ ≤ Real.exp (Cstar κ.u κ.ξ * (κ.Qbd : ℝ)) *
          (2 * (4 : ℝ) ^ s * 800) * ((2 : ℝ) ^ d * Real.exp (4 * κ.Kbd)) := by
        rw [hQeq]
        apply mul_le_mul _ hden hDPow (by positivity)
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [hc0, add_zero] using hτN.trans
          (mul_le_mul_of_nonneg_left hσN (by positivity))
      _ = _ := by rw [hh0, zero_add, Real.exp_add]; ring
  | lowDirect =>
    have hnclu : ¬ PT.tiling.mode.isCluster := by simp [hm, Mode.isCluster]
    have hnot : PT.tiling.mode ≠ .bounded := by simp [hm]
    obtain ⟨hcExp, hQExp⟩ := hunbounded hnot
    have hh0 := (D.tiling_valid.tiling_valid.direct_data (Or.inl hm) i).2.2.2.2.1
    have hcap := clean_prior_cap D v σ hσ G hG (hbud hnot).2.1 hG
    have hσN : (T.S.N k : ℝ) * σ x ≤ 2 * Real.exp G := by
      have hh := hcap x
      change (T.S.N k : ℝ) * σ x ≤ 2 ^ (PT.tiling.P i).h * (2 * Real.exp G) at hh
      simpa only [hh0, pow_zero, one_mul] using hh
    have hD : 1 / 2 + (PT.tiling.P i).g / (4 * T.S.n k) ≤ D₀ := by
      simp only [OwnDegOK, hm] at hOwn
      exact hOwn.1
    have hden := direct_bulk_denominator_saving (T.S.n k) d
      (PT.tiling.P i).g D₀ hn (Nat.cast_nonneg _) (hg hm) hdHalf hD
    have hcancel : Real.exp (5 * G) * Real.exp (-((PT.tiling.P i).g : ℝ) / 16) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      dsimp [G]
      simp only [Tiling.gain, hm]
      nlinarith [(Nat.cast_nonneg (PT.tiling.P i).g : (0 : ℝ) ≤ (PT.tiling.P i).g)]
    have hτBound : (T.S.N k : ℝ) * τ.w x ≤
        4 * (4 : ℝ) ^ s * Real.exp (4 * G) := by
      calc
        _ ≤ 2 * (4 : ℝ) ^ (s + c) * (2 * Real.exp G) :=
          hτN.trans (mul_le_mul_of_nonneg_left hσN (by positivity))
        _ ≤ 2 * ((4 : ℝ) ^ s * Real.exp (3 * G)) * (2 * Real.exp G) := by
          rw [pow_add]
          gcongr
        _ = _ := by rw [show 4 * G = 3 * G + G by ring, Real.exp_add]; ring
    change (T.S.N k : ℝ) * (Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) * τ.w x * D₀ ^ (-(d : ℝ))) ≤ _
    calc
      _ = Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) *
          ((T.S.N k : ℝ) * τ.w x) * D₀ ^ (-(d : ℝ)) := by ring
      _ ≤ Real.exp G * (4 * (4 : ℝ) ^ s * Real.exp (4 * G)) *
          ((2 : ℝ) ^ d * Real.exp (-((PT.tiling.P i).g : ℝ) / 16)) := by
        apply mul_le_mul _ hden hDPow (by positivity)
        exact mul_le_mul hQExp hτBound hNτ0 (Real.exp_pos G).le
      _ = 4 * (4 : ℝ) ^ s * (2 : ℝ) ^ d *
          (Real.exp (5 * G) * Real.exp (-((PT.tiling.P i).g : ℝ) / 16)) := by
        rw [show 5 * G = G + 4 * G by ring, Real.exp_add]; ring
      _ ≤ 4 * (4 : ℝ) ^ s * (2 : ℝ) ^ d := by
        simpa using mul_le_mul_of_nonneg_left hcancel (by positivity : 0 ≤ 4 * (4 : ℝ) ^ s * (2 : ℝ) ^ d)
      _ ≤ _ := by simp only [hh0, zero_add]; gcongr; nlinarith [hFixed]
  | lowCluster =>
    have hnot : PT.tiling.mode ≠ .bounded := by simp [hm]
    obtain ⟨hcExp, hQExp⟩ := hunbounded hnot
    have hσN := (hσ.2.2.choose_spec.2.2.1 (by simp [hm, Mode.isCluster])) x
    have hD : 1 / 2 - (10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb) / T.S.n k ≤ D₀ := by
      simp only [OwnDegOK, hm] at hOwn
      change |D₀ - 1 / 2| ≤ _ at hOwn
      have := (abs_le.mp hOwn).1
      linarith
    have hsmall : 4 * (10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb) ≤ T.S.n k := by
      have hh := hcluDrift hm
      change 40 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb ≤ G at hh
      linarith
    have hden := bounded_bulk_denominator_cost (T.S.n k) d
      (10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb) D₀ hn hd (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hsmall hD
    have hden' : D₀ ^ (-(d : ℝ)) ≤ (2 : ℝ) ^ d * Real.exp G := by
      apply hden.trans
      gcongr
      calc
        4 * (10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb) =
            40 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb := by ring
        _ ≤ G := hcluDrift hm
    have hcancel : Real.exp (5 * G) * Real.exp (-500 * G) ≤ 1 := by
      rw [← Real.exp_add]
      apply Real.exp_le_one_iff.2
      linarith
    have hτBound : (T.S.N k : ℝ) * τ.w x ≤
        2 * (4 : ℝ) ^ s * (2 : ℝ) ^ (PT.tiling.P i).h *
          (Real.exp (3 * G) * Real.exp (-500 * G)) := by
      calc
        _ ≤ 2 * (4 : ℝ) ^ (s + c) * ((2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (-500 * G)) :=
          hτN.trans (mul_le_mul_of_nonneg_left hσN (by positivity))
        _ ≤ 2 * ((4 : ℝ) ^ s * Real.exp (3 * G)) *
            ((2 : ℝ) ^ (PT.tiling.P i).h * Real.exp (-500 * G)) := by rw [pow_add]; gcongr
        _ = _ := by ring
    change (T.S.N k : ℝ) * (Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) * τ.w x * D₀ ^ (-(d : ℝ))) ≤ _
    calc
      _ = Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) *
          ((T.S.N k : ℝ) * τ.w x) * D₀ ^ (-(d : ℝ)) := by ring
      _ ≤ Real.exp G * (2 * (4 : ℝ) ^ s * (2 : ℝ) ^ (PT.tiling.P i).h *
          (Real.exp (3 * G) * Real.exp (-500 * G))) * ((2 : ℝ) ^ d * Real.exp G) := by
        apply mul_le_mul _ hden' hDPow (by positivity)
        exact mul_le_mul hQExp hτBound hNτ0 (Real.exp_pos G).le
      _ = 2 * (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P i).h + d) *
          (Real.exp (5 * G) * Real.exp (-500 * G)) := by
        rw [hpow2, show 5 * G = G + 3 * G + G by ring, Real.exp_add, Real.exp_add]; ring
      _ ≤ 2 * (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P i).h + d) := by
        simpa using mul_le_mul_of_nonneg_left hcancel (by positivity : 0 ≤ 2 * (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P i).h + d))
      _ ≤ _ := by gcongr; nlinarith [hFixed]
  | highDirect => have := D.mode_low; simp [Mode.isLow, hm] at this
  | highSmall => have := D.mode_low; simp [Mode.isLow, hm] at this
  | highLarge => have := D.mode_low; simp [Mode.isLow, hm] at this

/-- The late incidence saving turns the binary row factor into a polynomial gamma bound. -/
theorem late_saving_gamma_bound (n N m d R : ℕ) (C A : ℝ)
    (hn : 1 ≤ (n : ℝ)) (hN : (2 : ℝ) ^ n ≤ N) (hC : 0 ≤ C)
    (hCn : 2 * C ≤ n)
    (hInc : (m : ℝ) + d + A * Real.log n / 2 ≤ (n : ℝ) + 1)
    (hA : 3 * (R : ℝ) + 1 ≤ A * Real.log 2 / 2) :
    C * (2 : ℝ) ^ (m + d) / N ≤ (n : ℝ) ^ (-(3 * (R : ℝ))) := by
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity : 0 < (2 : ℝ) ^ n) hN
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hp (a : ℕ) : (2 : ℝ) ^ a = Real.exp ((a : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hNum : (2 : ℝ) ^ (m + d) ≤
      (2 : ℝ) ^ n * Real.exp ((1 - A * Real.log n / 2) * Real.log 2) := by
    rw [hp (m + d), hp n, ← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    have hh := mul_le_mul_of_nonneg_right hInc hlog2
    nlinarith
  have hRatio : (2 : ℝ) ^ (m + d) / N ≤
      Real.exp ((1 - A * Real.log n / 2) * Real.log 2) := by
    apply (div_le_iff₀ hN0).2
    apply hNum.trans
    convert mul_le_mul_of_nonneg_right hN (Real.exp_pos ((1 - A * Real.log n / 2) * Real.log 2)).le using 1 <;> ring
  have hDrift : Real.exp ((1 - A * Real.log n / 2) * Real.log 2) ≤
      2 * (n : ℝ) ^ (-(3 * (R : ℝ) + 1)) := by
    calc
      _ ≤ Real.exp (Real.log 2 + Real.log n * (-(3 * (R : ℝ) + 1))) := by
        apply Real.exp_le_exp.2
        have hh := mul_le_mul_of_nonneg_right hA hlogn
        nlinarith
      _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hn0]
  calc
    _ = C * ((2 : ℝ) ^ (m + d) / N) := by ring
    _ ≤ C * (2 * (n : ℝ) ^ (-(3 * (R : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (hRatio.trans hDrift) hC
    _ = (2 * C) * (n : ℝ) ^ (-(3 * (R : ℝ) + 1)) := by ring
    _ ≤ (n : ℝ) * (n : ℝ) ^ (-(3 * (R : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_right hCn (Real.rpow_nonneg hn0.le _)
    _ = _ := by
      conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hn0]
      congr 1
      ring

/-- Increasing the clique scale preserves the cleaned clique exclusion. -/
theorem noClique_raise {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (S : Finset (Fin N)) (π : Fin N → ℝ) (θ Q Q' : ℝ)
    (h : NoClique E c S π θ Q) (hQ : Q ≤ Q') : NoClique E c S π θ Q' := by
  classical
  rintro ⟨C, hCS, hcard, hclique⟩
  have hsize : ⌈Real.exp Q⌉₊ ≤ C.card := by
    rw [hcard]
    exact Nat.ceil_mono (Real.exp_le_exp.2 hQ)
  obtain ⟨C', hsub, hcard'⟩ := Finset.exists_subset_card_eq hsize
  exact h ⟨C', hsub.trans hCS, hcard', fun x hx z hz hne =>
    hclique x (hsub hx) z (hsub hz) hne⟩

/-- Count the actual unpinned crossing and bulk incidences without dropping multiplicity. -/
theorem unpinned_partition_counts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hq : D.L16QuantitativeValidity K) (v : Pos T k)
    (pins : Finset (Pos T k)) (hs : pins.card ≤ ListGateContext.pinBudget κ) :
    let U := {w : Pos T k // w ∈ D.externalEarly v \ pins}
    let c := Fintype.card {w : U // D.G.patchOf w.1 ≠ D.G.patchOf v}
    let d := Fintype.card {w : U // ¬ D.G.patchOf w.1 ≠ D.G.patchOf v}
    c ≤ (PT.tiling.P (D.G.patchOf v)).ℓ ∧ d ≤ (D.externalEarly v).card ∧
      T.S.n k - ((PT.tiling.P (D.G.patchOf v)).h +
        (PT.tiling.P (D.G.patchOf v)).ℓ + D.G.r + ListGateContext.pinBudget κ) ≤ d := by
  classical
  dsimp only
  let U := {w : Pos T k // w ∈ D.externalEarly v \ pins}
  let C := (D.externalEarly v \ pins).filter fun w => D.G.patchOf w ≠ D.G.patchOf v
  let B := (D.externalEarly v \ pins).filter fun w => ¬ D.G.patchOf w ≠ D.G.patchOf v
  let eC : {w : U // D.G.patchOf w.1 ≠ D.G.patchOf v} ≃ {w // w ∈ C} := {
    toFun := fun w => ⟨w.1.1, Finset.mem_filter.mpr ⟨w.1.2, w.2⟩⟩
    invFun := fun w => ⟨⟨w.1, (Finset.mem_filter.mp w.2).1⟩, (Finset.mem_filter.mp w.2).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let eB : {w : U // ¬ D.G.patchOf w.1 ≠ D.G.patchOf v} ≃ {w // w ∈ B} := {
    toFun := fun w => ⟨w.1.1, Finset.mem_filter.mpr ⟨w.1.2, w.2⟩⟩
    invFun := fun w => ⟨⟨w.1, (Finset.mem_filter.mp w.2).1⟩, (Finset.mem_filter.mp w.2).2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hCcard : Fintype.card {w : U // D.G.patchOf w.1 ≠ D.G.patchOf v} = C.card := by
    simpa using Fintype.card_congr eC
  have hBcard : Fintype.card {w : U // ¬ D.G.patchOf w.1 ≠ D.G.patchOf v} = B.card := by
    simpa using Fintype.card_congr eB
  change Fintype.card {w : U // D.G.patchOf w.1 ≠ D.G.patchOf v} ≤ _ ∧
    Fintype.card {w : U // ¬ D.G.patchOf w.1 ≠ D.G.patchOf v} ≤ _ ∧ _
  rw [hCcard, hBcard]
  obtain ⟨B₀, hB₀ext, hB₀patch, hB₀size, _, hC₀size⟩ :=
    Lane_q_s17_pool.lowGeom_bulk_early_candidates D D.tiling_valid hq.geometry.ids_injective v
  have hCsub : C ⊆ D.externalEarly v \ B₀ := by
    intro w hw
    obtain ⟨hwU, hwPatch⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hwU).1,
      fun hwB => hwPatch (hB₀patch w hwB)⟩
  have hBsub : B ⊆ D.externalEarly v := fun w hw =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).1
  have hB₀sub : B₀ \ pins ⊆ B := by
    intro w hw
    obtain ⟨hwB, hwPin⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hB₀ext hwB, hwPin⟩,
      fun hne => hne (hB₀patch w hwB)⟩
  refine ⟨(Finset.card_le_card hCsub).trans hC₀size, Finset.card_le_card hBsub, ?_⟩
  have h₁ := Finset.card_le_card hB₀sub
  have h₂ := Finset.card_sdiff_add_card_inter B₀ pins
  have h₃ := Finset.card_le_card (Finset.inter_subset_right (s₁ := B₀) (s₂ := pins))
  omega

/-- The actual late-role incidence saving makes every retained low-mode
homogeneous gamma polynomially small after one common index. -/
theorem eventually_retained_gamma (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (K : ℝ) (hK : 0 < K) (q₀ : ℝ) :
    ∀ᶠ k in atTop, ∀ (PT : ProfiledTiling κ T k)
      (D : ListGateContext κ T k PT) (hq : D.L16QuantitativeValidity K)
      (v : Pos T k) (heven : IsEvenRole v) (σ : Fin (T.S.N k) → ℝ)
      (hσ : D.CleanInitialPrior v σ) (a : PT.mesh.V) (ha : a ∈ PT.activeVertices)
      (τ : Law (T.S.N k)) (s c d : ℕ),
      s ≤ ListGateContext.pinBudget κ → c ≤ (PT.tiling.P (D.G.patchOf v)).ℓ →
      d ≤ (D.externalEarly v).card → (T.S.n k : ℝ) / 2 ≤ d →
      (∀ x, τ.w x ≤ 2 * (4 : ℝ) ^ (s + c) * σ x) →
      Real.exp (Cstar κ.u κ.ξ * ((PT.tiling.Q (D.G.patchOf v) : ℝ) + q₀)) *
        (PT.mesh.corner a (D.G.patchOf v)).sup'
          (D.tiling_valid.corner_clean _ a ha).nonempty (fun x => τ.w x *
            Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) (-(d : ℝ))) ≤
          (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) := by
  classical
  let C := (1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd)) *
    (4 : ℝ) ^ ListGateContext.pinBudget κ * Real.exp (Cstar κ.u κ.ξ * q₀)
  let Csmall := 1 + 4 * K + κ.a / 10 ^ 6
  have haPos : 0 < κ.a := by rw [hκ.a_eq]; exact div_pos hκ.θ_rng.1 (by norm_num)
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT := Real.tendsto_log_atTop.comp hnT
  have hlogSmall := Lane_q_s17_pool.eventually_log4_small T Csmall hCsmall
  have hRnat : 0 < κ.R := by
    rw [hκ.R_eq]
    exact Nat.pow_pos (by have := hκ.P_big.2; omega)
  have hR : (1 : ℝ) ≤ κ.R := by exact_mod_cast hRnat
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hA0 : 0 ≤ κ.A0 := by nlinarith [hκ.A0_big]
  have hA : 3 * (κ.R : ℝ) + 1 ≤ κ.A0 * Real.log 2 / 2 := by
    have hh := mul_le_mul_of_nonneg_left hlog2 hA0
    nlinarith [hκ.A0_big]
  filter_upwards [T.S.eventually_large 1 2, hlogSmall,
    hlogT.eventually_ge_atTop (1 : ℝ), hnT.eventually_ge_atTop (2 * C),
    hnT.eventually_ge_atTop (4 * κ.Kbd)] with k hn hsmall hy hCn hbd
  intro PT D hq v heven σ hσ a ha τ s c d hs hc hdExt hdHalf hτ
  let i := D.G.patchOf v
  let y := Real.log (T.S.n k : ℝ)
  have hn0 : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  have hn1 : (1 : ℝ) ≤ T.S.n k := by exact_mod_cast (by omega : 1 ≤ T.S.n k)
  have hy1 : 1 ≤ y := hy
  have hy4 : y ≤ y ^ 4 := by
    have h1 : (1 : ℝ) ≤ y ^ 3 := one_le_pow₀ hy1
    have hh := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ y)
    convert hh using 1 <;> ring
  have hhPower : Real.rpow y (1 / 10 : ℝ) ≤ y ^ 4 := by
    exact (Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)).trans_eq (Real.rpow_natCast y 4)
  have hhReal : ((PT.tiling.P i).h : ℝ) ≤ y ^ 4 :=
    (hq.geometry.height_bound i).trans hhPower
  have hh : (PT.tiling.P i).h ≤ T.S.n k := by
    have hcoef : 1 ≤ Csmall := by dsimp [Csmall]; linarith
    have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (y ^ 2))
    have hsmall' : Csmall * y ^ 4 ≤ (T.S.n k : ℝ) / 4 := hsmall
    have hreal : ((PT.tiling.P i).h : ℝ) ≤ T.S.n k := by nlinarith
    exact_mod_cast hreal
  obtain ⟨b, hb, _, _, _⟩ := hσ.2.2
  obtain ⟨x₀, hx₀⟩ := (D.tiling_valid.corner_clean i b hb).nonempty
  have hxenv : x₀ ∈ PT.envelope i := by
    rw [D.tiling_valid.envelope_eq]
    exact Finset.mem_biUnion.mpr ⟨b, hb, hx₀⟩
  have hgain0 := (low_mode_gain_budgets hκ D i).1
  have hGain : PT.tiling.gain i ≤ T.S.n k ∧
      (PT.tiling.mode = .lowDirect → ((PT.tiling.P i).g : ℝ) ≤ T.S.n k) := by
    cases hm : PT.tiling.mode with
    | bounded =>
      constructor
      · simpa [Tiling.gain, hm] using hn0.le
      · simp [hm]
    | lowDirect =>
      have hOwn := D.tiling_valid.envelope_degree i x₀ hxenv
      simp only [OwnDegOK, hm] at hOwn
      have hDrift := hq.geometry.degree_drift i x₀ hxenv
      have hDrift' : |deg (T.S.E k) PT.tiling.c (PT.π i).w x₀ - 1 / 2| ≤ K * y / T.S.n k := by
        apply (le_div_iff₀ hn0).2
        nlinarith [hDrift]
      have hhigh := (abs_le.mp hDrift').2
      have hg4 : ((PT.tiling.P i).g : ℝ) ≤ 4 * K * y := by
        have hm := (mul_le_mul_of_nonneg_right hOwn.1 hn0.le)
        have hc₁ : ((PT.tiling.P i).g : ℝ) / (4 * T.S.n k) * T.S.n k = (PT.tiling.P i).g / 4 := by field_simp <;> ring
        have hc₂ : K * Real.log (T.S.n k : ℝ) / T.S.n k * T.S.n k = K * y := by
          dsimp [y]; field_simp
        have ht := mul_le_mul_of_nonneg_right hhigh hn0.le
        nlinarith [hc₁, hc₂]
      have hsmall' : Csmall * y ^ 4 ≤ (T.S.n k : ℝ) / 4 := hsmall
      have hcoef : 4 * K ≤ Csmall := by dsimp [Csmall]; linarith
      have hgN : ((PT.tiling.P i).g : ℝ) ≤ T.S.n k := by
        have hm := mul_le_mul_of_nonneg_left hy4 hK.le
        have hm₂ := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ y ^ 4)
        nlinarith
      constructor
      · simpa [Tiling.gain, hm] using (show ((PT.tiling.P i).g : ℝ) / 1000 ≤ T.S.n k by linarith)
      · exact fun _ => hgN
    | lowCluster =>
      constructor
      · have hmul := mul_le_mul_of_nonneg_left hhReal (show 0 ≤ κ.a / 10 ^ 6 by positivity)
        have hcoef : κ.a / 10 ^ 6 ≤ Csmall := by dsimp [Csmall]; linarith
        have hm₂ := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ y ^ 4)
        have hsmall' : Csmall * y ^ 4 ≤ (T.S.n k : ℝ) / 4 := hsmall
        simp only [Tiling.gain, hm]
        nlinarith
      · simp [hm]
    | highDirect => have := D.mode_low; simp [Mode.isLow, hm] at this
    | highSmall => have := D.mode_low; simp [Mode.isLow, hm] at this
    | highLarge => have := D.mode_low; simp [Mode.isLow, hm] at this
  have hd : d ≤ T.S.n k := hdExt.trans (Lane_q_s17_pool.externalEarly_card_le D v)
  have hInc := externalEarly_late_budget D K hq v heven hh
  have hdR : (d : ℝ) ≤ (D.externalEarly v).card := by exact_mod_cast hdExt
  have hInc' : ((PT.tiling.P i).h : ℝ) + d + κ.A0 * Real.log (T.S.n k : ℝ) / 2 ≤
      (T.S.n k : ℝ) + 1 := by linarith
  have hLate := late_saving_gamma_bound (T.S.n k) (T.S.N k) (PT.tiling.P i).h d κ.R C κ.A0
    hn1 (by simpa [LargeHost] using hn.2.1) hC hCn hInc' hA
  have hN0 : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  rw [mul_comm]
  apply (le_div_iff₀ (Real.exp_pos _)).mp
  apply Finset.sup'_le
  intro x hx
  apply (le_div_iff₀ (Real.exp_pos _)).2
  have hxenv : x ∈ PT.envelope i := by
    rw [D.tiling_valid.envelope_eq]
    exact Finset.mem_biUnion.mpr ⟨a, ha, hx⟩
  have hPoint := low_mode_gamma_numerator hκ D v σ hσ τ s c d hc hd hdHalf hn0 hbd
    hGain.2
    hGain.1 x hxenv (hτ x)
  have hPointDiv : Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) * τ.w x *
      Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π i).w x) (-(d : ℝ)) ≤
      (1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd)) *
        (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P i).h + d) / T.S.N k := by
    apply (le_div_iff₀ hN0).2
    nlinarith [hPoint]
  calc
    _ = Real.exp (Cstar κ.u κ.ξ * q₀) *
        (Real.exp (Cstar κ.u κ.ξ * (PT.tiling.Q i : ℝ)) * τ.w x *
          Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π i).w x) (-(d : ℝ))) := by
      rw [mul_add, Real.exp_add]; ring
    _ ≤ Real.exp (Cstar κ.u κ.ξ * q₀) *
        ((1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd)) *
          (4 : ℝ) ^ s * (2 : ℝ) ^ ((PT.tiling.P i).h + d) / T.S.N k) :=
      mul_le_mul_of_nonneg_left hPointDiv (Real.exp_pos _).le
    _ ≤ C * (2 : ℝ) ^ ((PT.tiling.P i).h + d) / T.S.N k := by
      dsimp [C]
      rw [show Real.exp (Cstar κ.u κ.ξ * q₀) *
          (1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd) * (4 : ℝ) ^ s *
            (2 : ℝ) ^ ((PT.tiling.P i).h + d) / T.S.N k) =
          (1600 * Real.exp (Cstar κ.u κ.ξ * κ.Qbd + 4 * κ.Kbd) * (4 : ℝ) ^ s *
            Real.exp (Cstar κ.u κ.ξ * q₀)) * (2 : ℝ) ^ ((PT.tiling.P i).h + d) / T.S.N k by ring]
      gcongr <;> norm_num
    _ ≤ _ := hLate

/-- A fixed increase in the clique scale meets S12's scale threshold and
costs only a fixed factor in gamma. -/
noncomputable def raisedCornerHomogeneousInput {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k)
    (a : PT.mesh.V) (ha : a ∈ PT.activeVertices) (τ : Law (T.S.N k))
    (d : ℕ) (hd : d ≤ T.S.n k)
    (hτ : τ.SupportedIn (PT.mesh.corner a (D.G.patchOf v)))
    (hτwidth : τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (hπwidth : (PT.π (D.G.patchOf v)).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (C0 : ℝ)
    (hGate : ∀ x ∈ PT.mesh.corner a (D.G.patchOf v),
      S12.DegGate (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w C0 (bstar T k) x)
    (hPos : ∀ x ∈ PT.mesh.corner a (D.G.patchOf v),
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x)
    (q₀ : ℝ)
    (hq₀ : Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ q₀ ∧ 1 ≤ q₀)
    (γ : ℝ)
    (hγ : γ = Real.exp (Cstar κ.u κ.ξ * ((PT.tiling.Q (D.G.patchOf v) : ℝ) + q₀)) *
      (PT.mesh.corner a (D.G.patchOf v)).sup'
        (D.tiling_valid.corner_clean _ a ha).nonempty (fun x => τ.w x *
          Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) (-(d : ℝ))))
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    S12.HomogeneousInput κ hκ T k PT.tiling.c C0 := by
  let i := D.G.patchOf v
  have hClean := D.tiling_valid.corner_clean i a ha
  have hSp : PT.mesh.corner a i ⊆ T.X k := by
    intro x hx
    exact (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports i).2.1
      ((D.tiling_valid.tiling_valid.patch_supports i).1 (hClean.sub hx)))).1
  have hπY : (PT.π i).SupportedIn (T.Y k) := by
    intro y hy
    apply D.tiling_valid.law_supported i y
    intro hyY
    exact hy (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports i).2.2.2
      ((D.tiling_valid.tiling_valid.patch_supports i).2.2.1 hyY))).1
  refine {
    S := {
      d := d
      d_le := hd
      τ := τ
      π := fun _ => PT.π i
      τ_supp := fun x hx => hτ x (fun hxSp => hx (hSp hxSp))
      π_supp := fun _ => hπY
      τ_width := hτwidth
      π_width := fun _ => hπwidth }
    π := PT.π i
    homogeneous := fun _ => rfl
    Sp := PT.mesh.corner a i
    Sp_nonempty := hClean.nonempty
    Sp_subset := hSp
    τ_supported := hτ
    π_supported := hπY
    degree_gate := hGate
    degree_positive := hPos
    Q := (PT.tiling.Q i : ℝ) + q₀
    Q_large := ⟨by linarith [hq₀.1, (Nat.cast_nonneg (PT.tiling.Q i) : (0 : ℝ) ≤ PT.tiling.Q i)],
      by linarith [hq₀.2, (Nat.cast_nonneg (PT.tiling.Q i) : (0 : ℝ) ≤ PT.tiling.Q i)]⟩
    noClique := noClique_raise _ _ _ _ _ _ _ hClean.noClique (by linarith [hq₀.2])
    gamma := γ
    gamma_eq := hγ
    gamma_nonneg := hγ0
    gamma_lt_one := hγ1 }

/-- The short pin and crossing costs fit the common first-side atom budget. -/
theorem short_restriction_cap_bound (s s₀ c h : ℕ) (K y wS : ℝ)
    (hs : s ≤ s₀) (hK : 0 ≤ K) (hy : 1 ≤ y)
    (hc : (c : ℝ) ≤ K * Real.sqrt y) (hh : (h : ℝ) ≤ Real.rpow y (1 / 10 : ℝ))
    (hroom : (4 + 3 * (s₀ : ℝ) + 8 * K) * (1 + y) ≤ wS) :
    2 * (4 : ℝ) ^ s * (8 : ℝ) ^ c *
      ((2 : ℝ) ^ h * (2 * Real.exp (K * Real.sqrt y))) ≤ Real.exp wS := by
  have powBound (b L : ℝ) (hb : 0 < b) (hlog : Real.log b ≤ L) (a : ℕ) :
      b ^ a ≤ Real.exp ((a : ℝ) * L) := by
    have heq : Real.exp ((a : ℝ) * Real.log b) = b ^ a := by rw [Real.exp_nat_mul, Real.exp_log hb]
    rw [← heq]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg a))
  have hlog (b : ℝ) (hb : 0 < b) : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hb
  have h4 : (4 : ℝ) ≤ Real.exp 3 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    apply Real.exp_le_exp.2
    have := hlog 4 (by norm_num)
    linarith
  have h4s := powBound 4 3 (by norm_num) (by have := hlog 4 (by norm_num); linarith) s
  have h8c := powBound 8 7 (by norm_num) (by have := hlog 8 (by norm_num); linarith) c
  have h2h := powBound 2 1 (by norm_num) (by have := hlog 2 (by norm_num); linarith) h
  have h4s' : (4 : ℝ) ^ s ≤ Real.exp (3 * (s : ℝ)) := by convert h4s using 1 <;> ring
  have h8c' : (8 : ℝ) ^ c ≤ Real.exp (7 * (c : ℝ)) := by convert h8c using 1 <;> ring
  have h2h' : (2 : ℝ) ^ h ≤ Real.exp (h : ℝ) := by simpa using h2h
  have hsR : (s : ℝ) ≤ s₀ := by exact_mod_cast hs
  have hsqrt : Real.sqrt y ≤ y := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  have hhY : (h : ℝ) ≤ y := hh.trans
    ((Real.rpow_le_rpow_of_exponent_le hy (by norm_num)).trans_eq (Real.rpow_one y))
  calc
    _ = 4 * (4 : ℝ) ^ s * (8 : ℝ) ^ c * (2 : ℝ) ^ h * Real.exp (K * Real.sqrt y) := by ring
    _ ≤ Real.exp 3 * Real.exp (3 * (s : ℝ)) * Real.exp (7 * (c : ℝ)) *
        Real.exp (h : ℝ) * Real.exp (K * Real.sqrt y) := by
      gcongr
    _ = Real.exp (3 + 3 * (s : ℝ) + 7 * (c : ℝ) + (h : ℝ) + K * Real.sqrt y) := by
      repeat rw [← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have hKy := mul_le_mul_of_nonneg_left hsqrt hK
      nlinarith [hroom]

/-- Logarithmic short-exposure costs fit any positive power width. -/
theorem eventually_short_width_room (T : Stage) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C) :
    ∀ᶠ k in atTop, C * (1 + Real.log (T.S.n k : ℝ)) ≤ (T.S.n k : ℝ) ^ r := by
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT := Real.tendsto_log_atTop.comp hnT
  have hLittle := (isLittleO_log_rpow_atTop hr).const_mul_left (2 * C)
  have hEvent := hnT.eventually (hLittle.def (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hEvent, hlogT.eventually_ge_atTop (1 : ℝ), hnT.eventually_ge_atTop (1 : ℝ)] with k hk hy hn
  have hpow : 0 ≤ (T.S.n k : ℝ) ^ r := Real.rpow_nonneg (by positivity) _
  have hy' : 1 ≤ Real.log (T.S.n k : ℝ) := hy
  have hlogn : 0 ≤ Real.log (T.S.n k : ℝ) := by linarith
  have hbound : 2 * C * Real.log (T.S.n k : ℝ) ≤ (T.S.n k : ℝ) ^ r := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hC, abs_of_nonneg hlogn,
      abs_of_nonneg hpow] using hk
  nlinarith

/-- Row mass on an arbitrary finite incidence type. -/
noncomputable def finiteRowMass {N : ℕ} {I α : Type*} [Fintype I]
    (μ : Law N) (f : I → Fin N → α → ℝ) (ys : I → α) : ℝ :=
  ∑ x, μ.w x * ∏ i, f i x (ys i)

/-- Reindexing incidences by an equivalence preserves their row mass. -/
theorem finiteRowMass_reindex {N : ℕ} {I J α : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (μ : Law N) (f : J → Fin N → α → ℝ) (zs : I → α) :
    finiteRowMass μ f (fun j => zs (e.symm j)) =
      finiteRowMass μ (fun i => f (e i)) zs := by
  classical
  unfold finiteRowMass
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  exact (Fintype.prod_equiv e _ _ (fun i => by simp)).symm

/-- Two successive finite experiments add their failure budgets, retaining
the actual normalized crossing row in the bulk experiment. -/
theorem crossing_bulk_failure_bound {N : ℕ} {C B α β : Type*}
    [Fintype C] [Fintype B] [Fintype α] [Fintype β]
    [instC : DecidableEq C] [instB : DecidableEq B] (μ : Law N)
    (P : FinLaw (C → α)) (R : FinLaw (B → β))
    (f : C → Fin N → α → ℝ) (g : B → Fin N → β → ℝ)
    (hf : ∀ i x y, 0 ≤ f i x y) (ε δ : ℝ) (hδ : 0 ≤ δ)
    (hCross : P.pr (fun ys => finiteRowMass μ f ys < 15 / 16) ≤ ε)
    (hBulk : ∀ (ys : C → α) (τ : Law N),
      15 / 16 ≤ finiteRowMass μ f ys →
      (∀ x, finiteRowMass μ f ys * τ.w x = μ.w x * ∏ i, f i x (ys i)) →
      R.pr (fun zs => finiteRowMass τ g zs < 2 / 3) ≤ δ) :
    P.E (fun ys => R.pr (fun zs =>
      (∑ x, μ.w x * (∏ i, f i x (ys i)) * ∏ j, g j x (zs j)) < 4 / 7)) ≤ ε + δ := by
  classical
  letI : DecidableEq C := instC
  letI : DecidableEq B := instB
  let Z := finiteRowMass μ f
  have hinner (ys : C → α) : R.pr (fun zs =>
      (∑ x, μ.w x * (∏ i, f i x (ys i)) * ∏ j, g j x (zs j)) < 4 / 7) ≤
      (if Z ys < 15 / 16 then 1 else 0) + δ := by
    by_cases hbad : Z ys < 15 / 16
    · simp only [hbad, ite_true]
      have hpr : R.pr (fun zs =>
          (∑ x, μ.w x * (∏ i, f i x (ys i)) * ∏ j, g j x (zs j)) < 4 / 7) ≤ 1 := by
        unfold FinLaw.pr
        apply le_trans (Finset.sum_le_sum (fun z _ => ?_)) R.sum_one.le
        split_ifs <;> simp [R.nonneg]
      linarith
    · have hZlower : 15 / 16 ≤ Z ys := le_of_not_gt hbad
      have hZ : 0 < Z ys := lt_of_lt_of_le (by norm_num) hZlower
      let F : Fin N → ℝ := fun x => ∏ i, f i x (ys i)
      have hF : ∀ x, 0 ≤ F x := fun x => Finset.prod_nonneg (fun i _ => hf i x _)
      let τ := Lane_q_s17_pool.reweightLaw μ F hF (Z ys) hZ rfl
      have hrow (x : Fin N) : Z ys * τ.w x = μ.w x * ∏ i, f i x (ys i) := by
        dsimp [τ, Lane_q_s17_pool.reweightLaw, F]
        field_simp
      have hTail := hBulk ys τ hZlower hrow
      have hsub : R.pr (fun zs =>
          (∑ x, μ.w x * (∏ i, f i x (ys i)) * ∏ j, g j x (zs j)) < 4 / 7) ≤
          R.pr (fun zs => finiteRowMass τ g zs < 2 / 3) := by
        apply Lane_q_s17_pool.pr_mono
        intro zs hz
        have hmass : (∑ x, μ.w x * (∏ i, f i x (ys i)) * ∏ j, g j x (zs j)) =
            Z ys * finiteRowMass τ g zs := by
          unfold finiteRowMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [← mul_assoc, hrow x]
        rw [hmass] at hz
        by_contra hnot
        have hh := mul_le_mul hZlower (le_of_not_gt hnot) (by norm_num : (0 : ℝ) ≤ 2 / 3) hZ.le
        norm_num at hh
        linarith
      simpa [hbad] using hsub.trans hTail
  calc
    _ ≤ P.E (fun ys => (if Z ys < 15 / 16 then 1 else 0) + δ) := by
      unfold FinLaw.E
      exact Finset.sum_le_sum (fun ys _ => mul_le_mul_of_nonneg_left (hinner ys) (P.nonneg ys))
    _ = P.pr (fun ys => Z ys < 15 / 16) + δ := by
      unfold FinLaw.E FinLaw.pr
      simp_rw [mul_add, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
    _ ≤ _ := by change P.pr (fun ys => finiteRowMass μ f ys < 15 / 16) + δ ≤ ε + δ; linarith

abbrev UnpinnedEarly {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k) (pins : Finset (Pos T k)) :=
  {w : Pos T k // w ∈ D.externalEarly v \ pins}

abbrev CrossingEarly {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k) (pins : Finset (Pos T k)) :=
  {w : UnpinnedEarly D v pins // D.G.patchOf w.1 ≠ D.G.patchOf v}

abbrev BulkEarly {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k) (pins : Finset (Pos T k)) :=
  {w : UnpinnedEarly D v pins // ¬ D.G.patchOf w.1 ≠ D.G.patchOf v}

noncomputable def unpinnedCrossingLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (pins : Finset (Pos T k)) :
    FinLaw (CrossingEarly D v pins → Fin (T.S.N k)) :=
  FinLaw.pi fun w => ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1.1))

noncomputable def unpinnedBulkLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (pins : Finset (Pos T k)) :
    FinLaw (BulkEarly D v pins → Fin (T.S.N k)) :=
  FinLaw.pi fun w => ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1.1))

/-- Normalize the actual pinned row, retaining seven eighths of its initial mass and its pointwise cap. -/
theorem pin_row_mass_setup {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (pins : Finset (Pos T k)) (hPins : pins ⊆ D.externalEarly v)
    (fixed : Pos T k → Fin (T.S.N k)) (s₀ : ℕ) (hs : pins.card ≤ s₀)
    (hMass : (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤ D.pinnedPriorMass v σ pins fixed)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 4)
    (hsmall : 2 * (s₀ : ℝ) * δ ≤ 1 / 100) (hB : 0 ≤ B)
    (hcap : (cleanPriorLaw D v σ hσ).CapLE B)
    (hdeg : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v,
      |deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x - 1 / 2| ≤ δ) :
    ∃ (μ : Law (T.S.N k)) (Z : ℝ),
      7 / 8 ≤ Z ∧ μ.CapLE (2 * (4 : ℝ) ^ pins.card * B) ∧
      (∀ x, Z * μ.w x = σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w)) ∧
      (∀ x, μ.w x ≤ 2 * (4 : ℝ) ^ pins.card * σ x) := by
  classical
  let Z := ∑ x, σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w)
  have hmax : 0 < (1 / 2 : ℝ) + δ := by linarith
  have hdegree : ∀ x, σ x ≠ 0 → ∀ w ∈ pins,
      (1 / 4 : ℝ) ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ∧
      deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x ≤ 1 / 2 + δ := by
    intro x hx w hw
    obtain ⟨hl, hu⟩ := abs_le.mp (hdeg x hx w (hPins hw))
    constructor <;> linarith
  have hZlower : (7 / 8 : ℝ) ≤ Z := by
    have h₁ := pinned_mass_seven_eighths pins.card s₀ δ hs hδ hsmall hδsmall
    have h₂ := div_le_div_of_nonneg_right hMass (pow_nonneg hmax.le pins.card)
    have h₃ := pinned_restriction_mass_lower D v σ hσ pins fixed (1 / 2 + δ) hmax
      (fun x hx w hw => ⟨lt_of_lt_of_le (by norm_num) (hdegree x hx w hw).1,
        (hdegree x hx w hw).2⟩)
    exact h₁.trans (h₂.trans h₃)
  have hZ : 0 < Z := lt_of_lt_of_le (by norm_num) hZlower
  obtain ⟨μ, _, hμcap, hrow⟩ := normalize_pinned_restriction D v σ hσ pins fixed B
    (1 / 4) Z hB (by norm_num) hZ hcap rfl (fun x hx w hw => (hdegree x hx w hw).1)
  refine ⟨μ, Z, hZlower, ?_, hrow, ?_⟩
  · intro x
    apply (hμcap x).trans
    norm_num
    apply (div_le_iff₀ hZ).2
    have hMul := mul_le_mul_of_nonneg_left hZlower (show 0 ≤ 2 * (4 : ℝ) ^ pins.card * B by positivity)
    have hBP : 0 ≤ B * (4 : ℝ) ^ pins.card := by positivity
    nlinarith
  · intro x
    by_cases hz : σ x = 0
    · have hh := hrow x
      rw [hz, zero_mul] at hh
      have hμzero := (mul_eq_zero.mp hh).resolve_left hZ.ne'
      simp [hz, hμzero]
    · have hProd : (∏ w ∈ pins, D.hitRatio w x (fixed w)) ≤ (4 : ℝ) ^ pins.card := by
        calc
          _ ≤ ∏ _w ∈ pins, (4 : ℝ) := by
            apply Finset.prod_le_prod₀ (fun w _ => hitRatio_nonneg D _ _ _)
            intro w hw
            unfold ListGateContext.hitRatio
            have hd := (hdegree x hz w hw).1
            have hdp : 0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x :=
              lt_of_lt_of_le (by norm_num) hd
            calc
              _ ≤ 1 / deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x :=
                div_le_div_of_nonneg_right (by unfold hit; split_ifs <;> norm_num) hdp.le
              _ ≤ 1 / (1 / 4 : ℝ) := one_div_le_one_div_of_le (by norm_num) hd
              _ = 4 := by norm_num
          _ = _ := by simp
      have hh := mul_le_mul_of_nonneg_left hProd (hσ.1 x)
      have hlower := mul_le_mul_of_nonneg_right hZlower (μ.nonneg x)
      nlinarith [hrow x, μ.nonneg x]

/-- The normalized row after successful pins and crossings is bounded by the original cleaned prior. -/
theorem post_crossing_domination {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : ∀ x, 0 ≤ σ x)
    (μ τ : Law (T.S.N k)) (pins : Finset (Pos T k))
    (hPins : pins ⊆ D.externalEarly v) (fixed : Pos T k → Fin (T.S.N k))
    (ys : CrossingEarly D v pins → Fin (T.S.N k))
    (Zp Zc : ℝ) (hZp : 7 / 8 ≤ Zp) (hZc : 15 / 16 ≤ Zc)
    (hpin : ∀ x, Zp * μ.w x = σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w))
    (hcross : ∀ x, Zc * τ.w x = μ.w x * ∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w))
    (hcap : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v, ∀ y, D.hitRatio w x y ≤ 4) :
    ∀ x, τ.w x ≤ 2 * (4 : ℝ) ^ (pins.card + Fintype.card (CrossingEarly D v pins)) * σ x := by
  classical
  intro x
  have hZprod : (1 / 2 : ℝ) ≤ Zp * Zc := by
    have hh := mul_le_mul hZp hZc (by norm_num : (0 : ℝ) ≤ 15 / 16) (by linarith : 0 ≤ Zp)
    norm_num at hh
    linarith
  have hrow : (Zp * Zc) * τ.w x = σ x *
      (∏ w ∈ pins, D.hitRatio w x (fixed w)) *
        ∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w) := by
    calc
      _ = Zp * (Zc * τ.w x) := by ring
      _ = Zp * (μ.w x * ∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w)) := by rw [hcross x]
      _ = (Zp * μ.w x) * ∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w) := by ring
      _ = _ := by rw [hpin x]
  by_cases hz : σ x = 0
  · rw [hz, zero_mul, zero_mul] at hrow
    have hτzero : τ.w x = 0 := (mul_eq_zero.mp hrow).resolve_left (by linarith : Zp * Zc ≠ 0)
    simp [hz, hτzero]
  · have hpinProd : (∏ w ∈ pins, D.hitRatio w x (fixed w)) ≤ (4 : ℝ) ^ pins.card := by
      calc
        _ ≤ ∏ _w ∈ pins, (4 : ℝ) := Finset.prod_le_prod₀
          (fun w _ => hitRatio_nonneg D w x _) (fun w hw => hcap x hz w (hPins hw) _)
        _ = _ := by simp
    have hcrossProd : (∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w)) ≤
        (4 : ℝ) ^ Fintype.card (CrossingEarly D v pins) := by
      calc
        _ ≤ ∏ _w : CrossingEarly D v pins, (4 : ℝ) := Finset.prod_le_prod₀
          (fun w _ => hitRatio_nonneg D _ x _) (fun w _ => hcap x hz w.1.1
            (Finset.mem_sdiff.mp w.1.2).1 _)
        _ = _ := by simp
    have hprod := mul_le_mul hpinProd hcrossProd
      (Finset.prod_nonneg (fun w _ => hitRatio_nonneg D _ x _)) (by positivity)
    rw [← pow_add] at hprod
    have hh := mul_le_mul_of_nonneg_left hprod (hσ x)
    have hlow := mul_le_mul_of_nonneg_right hZprod (τ.nonneg x)
    nlinarith [hrow]

/-- The crossing adapter uses the actual independent external laws and
the cleaned corner, with their preserved incidence multiplicity. -/
theorem unpinned_crossing_tail {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (pins : Finset (Pos T k)) (μ : Law (T.S.N k))
    (X : Finset (Fin (T.S.N k))) (hX : X ⊆ T.X k)
    (hXenv : X ⊆ PT.envelope (D.G.patchOf v)) (hμ : μ.SupportedIn X)
    (wS wL err W : ℝ) (hDisc : TwoBudgetDisc T k wS wL err)
    (he : 0 ≤ err) (heb : err ≤ bstar T k) (hb : bstar T k ≤ 1 / 16)
    (hc : 8 * (Fintype.card (CrossingEarly D v pins) : ℝ) * bstar T k ≤ 1 / 16)
    (hcap : μ.CapLE (Real.exp wS *
      ((((1 / 2 : ℝ) - err) / (1 / 2 + 3 * bstar T k)) / 4) ^
        Fintype.card (CrossingEarly D v pins)))
    (hν : ∀ i, (PT.π i).WidthLE W) :
    (unpinnedCrossingLaw D v pins).pr (fun ys =>
      finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys < 15 / 16) ≤
        (Fintype.card (CrossingEarly D v pins) : ℝ) * (2 * Real.exp (W - wL)) := by
  classical
  let c := Fintype.card (CrossingEarly D v pins)
  let e : Fin c ≃ CrossingEarly D v pins := (Fintype.equivFin _).symm
  let ν : Fin c → Law (T.S.N k) := fun i => PT.π (D.G.patchOf (e i).1.1)
  let den : Fin c → Fin (T.S.N k) → ℝ := fun i x =>
    deg (T.S.E k) PT.tiling.c (ν i).w x
  have hbstar : 0 ≤ bstar T k := by unfold bstar; positivity
  have hε : 0 < (1 / 2 : ℝ) - err := by linarith
  have hmax : 0 < (1 / 2 : ℝ) + 3 * bstar T k := by linarith
  have hdegrees (i : Fin c) (x : Fin (T.S.N k)) (hx : x ∈ X) :
      (1 / 4 : ℝ) ≤ den i x ∧ den i x ≤ 1 / 2 + 3 * bstar T k := by
    have hh := D.tiling_valid.envelope_other_degree (D.G.patchOf v) (D.G.patchOf (e i).1.1)
      (e i).2 x (hXenv hx)
    dsimp [den, ν]
    obtain ⟨h₁, h₂⟩ := abs_le.mp hh
    constructor <;> linarith
  have hνY (i : Fin c) : (ν i).SupportedIn (T.Y k) := by
    intro y hy
    apply D.tiling_valid.law_supported _ y
    intro hh
    exact hy (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports _).2.2.2
      ((D.tiling_valid.tiling_valid.patch_supports _).2.2.1 hh))).1
  have hTail := independent_hitRatios_lower_tail hDisc PT.tiling.c X hX μ ν den hμ
    (by norm_num : (0 : ℝ) < 1 / 4) hmax hε
    (by rw [one_div_div]; apply (div_le_iff₀ hmax).2; linarith)
    (by simpa [c] using hcap)
    (fun i x hx => (hdegrees i x hx).1) (fun i x hx => (hdegrees i x hx).2)
    hνY (fun i => hν _)
  have hRetain := crossing_mass_fifteen_sixteenths c (bstar T k) err hbstar he heb hb hc
  unfold unpinnedCrossingLaw
  rw [pi_pr_equiv e]
  have hmass (ys : Fin c → Fin (T.S.N k)) :
      finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1)
        (fun w => ys (e.symm w)) =
      productMass μ (fun i x y => if x ∈ X then hit (T.S.E k) PT.tiling.c x y / den i x else 0) ys := by
    rw [finiteRowMass_reindex e]
    unfold finiteRowMass productMass
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxX : x ∈ X
    · simp only [hxX, ite_true]
      rfl
    · simp [hμ x hxX, hxX]
  have hsub : (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr
      (fun ys => finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1)
        (fun w => ys (e.symm w)) < 15 / 16) ≤
      (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr
        (fun ys => productMass μ (fun i x y => if x ∈ X then
          hit (T.S.E k) PT.tiling.c x y / den i x else 0) ys <
          (((1 / 2 : ℝ) - err) / (1 / 2 + 3 * bstar T k)) ^ c) := by
    apply Lane_q_s17_pool.pr_mono
    intro ys hy
    rw [hmass] at hy
    exact hy.trans_le hRetain
  exact hsub.trans hTail

/-- Apply S12 to the actual homogeneous bulk incidences on the original cleaned corner. -/
theorem unpinned_bulk_tail {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (v : Pos T k) (pins : Finset (Pos T k))
    (a : PT.mesh.V) (ha : a ∈ PT.activeVertices) (τ : Law (T.S.N k))
    (hd : Fintype.card (BulkEarly D v pins) ≤ T.S.n k)
    (hτ : τ.SupportedIn (PT.mesh.corner a (D.G.patchOf v)))
    (hτwidth : τ.WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (hπwidth : (PT.π (D.G.patchOf v)).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)))
    (hGate : ∀ x ∈ PT.mesh.corner a (D.G.patchOf v),
      S12.DegGate (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w 1 (bstar T k) x)
    (hPos : ∀ x ∈ PT.mesh.corner a (D.G.patchOf v),
      0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x)
    (q₀ : ℝ)
    (hq₀ : Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ q₀ ∧ 1 ≤ q₀)
    (hγ : Real.exp (Cstar κ.u κ.ξ * ((PT.tiling.Q (D.G.patchOf v) : ℝ) + q₀)) *
      (PT.mesh.corner a (D.G.patchOf v)).sup' (D.tiling_valid.corner_clean _ a ha).nonempty
        (fun x => τ.w x * Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x)
          (-(Fintype.card (BulkEarly D v pins) : ℝ))) ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))))
    (hSmall : (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) < 1)
    (hTail : ∀ H : S12.HomogeneousInput κ hκ T k PT.tiling.c 1,
      (FinLaw.pi fun _ : Fin H.S.d => ListGateContext.lawAsFinLaw H.π).pr
        (fun ys => productMass H.S.τ (fun _ x y =>
          hit (T.S.E k) PT.tiling.c x y / deg (T.S.E k) PT.tiling.c H.π.w x) ys < 2 / 3) ≤
      (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) *
        ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma)) :
    (unpinnedBulkLaw D v pins).pr (fun ys =>
      finiteRowMass τ (fun w : BulkEarly D v pins => D.hitRatio w.1.1) ys < 2 / 3) ≤
        (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) *
          ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
            4 ^ (κ.u + 1) * (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ)))) := by
  classical
  let d := Fintype.card (BulkEarly D v pins)
  let γ := Real.exp (Cstar κ.u κ.ξ * ((PT.tiling.Q (D.G.patchOf v) : ℝ) + q₀)) *
    (PT.mesh.corner a (D.G.patchOf v)).sup' (D.tiling_valid.corner_clean _ a ha).nonempty
      (fun x => τ.w x * Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) (-(d : ℝ)))
  have hγ0 : 0 ≤ γ := by
    apply mul_nonneg (Real.exp_pos _).le
    obtain ⟨x, hx⟩ := (D.tiling_valid.corner_clean _ a ha).nonempty
    have hdeg0 : 0 ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x := by
      unfold deg
      exact Finset.sum_nonneg (fun y _ => mul_nonneg ((PT.π _).nonneg y)
        (by unfold hit; split_ifs <;> norm_num))
    have hnonneg : 0 ≤ τ.w x * Real.rpow
        (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) (-(d : ℝ)) :=
      mul_nonneg (τ.nonneg x) (Real.rpow_nonneg hdeg0 _)
    exact hnonneg.trans (Finset.le_sup' (fun z => τ.w z * Real.rpow
      (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w z) (-(d : ℝ))) hx)
  let H := raisedCornerHomogeneousInput hκ D v a ha τ d hd hτ hτwidth hπwidth 1
    hGate hPos q₀ hq₀ γ rfl hγ0 (hγ.trans_lt hSmall)
  have hBound := hTail H
  have hγH : H.gamma ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) := hγ
  have hInner : (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma ≤
      (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left hγH (by positivity : 0 ≤ (4 : ℝ) ^ (κ.u + 1))
    linarith
  have hFinal := hBound.trans (mul_le_mul_of_nonneg_left hInner
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 2 / 3) _))
  let e : Fin d ≃ BulkEarly D v pins := (Fintype.equivFin _).symm
  have hpatch (w : BulkEarly D v pins) : D.G.patchOf w.1.1 = D.G.patchOf v := not_ne_iff.mp w.2
  have hP : (fun w : BulkEarly D v pins => ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1.1))) =
      (fun _ : BulkEarly D v pins => ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf v))) := by
    funext w
    rw [hpatch w]
  unfold unpinnedBulkLaw
  rw [hP, pi_pr_equiv e]
  have hmass (ys : Fin d → Fin (T.S.N k)) :
      finiteRowMass τ (fun w : BulkEarly D v pins => D.hitRatio w.1.1) (fun w => ys (e.symm w)) =
      productMass τ (fun _ x y => hit (T.S.E k) PT.tiling.c x y /
        deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x) ys := by
    rw [finiteRowMass_reindex e]
    unfold finiteRowMass productMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    apply Fintype.prod_congr
    intro i
    simp only [ListGateContext.hitRatio, hpatch]
  simp_rw [hmass]
  exact hFinal

/-- Reserve the atom budget needed by all intermediate normalized crossing rows. -/
theorem pinned_cap_for_crossing {N s c : ℕ} (μ : Law N) (B wS q : ℝ)
    (hB : 0 ≤ B) (hq : 1 / 2 ≤ q)
    (hμ : μ.CapLE (2 * (4 : ℝ) ^ s * B))
    (hshort : 2 * (4 : ℝ) ^ s * (8 : ℝ) ^ c * B ≤ Real.exp wS) :
    μ.CapLE (Real.exp wS * (q / 4) ^ c) := by
  have h8 : 0 < (8 : ℝ) ^ c := by positivity
  have hBbound : 2 * (4 : ℝ) ^ s * B ≤ Real.exp wS * (1 / 8 : ℝ) ^ c := by
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    apply (le_div_iff₀ h8).2
    nlinarith [hshort]
  intro x
  apply (hμ x).trans
  apply hBbound.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact pow_le_pow_left₀ (by norm_num) (by linarith) c

/-- The same short-exposure budget gives the final normalized row the
width required by the homogeneous bulk estimate. -/
theorem retained_row_width {N s c : ℕ} (σ τ : Law N) (B wS w : ℝ)
    (hN : 0 < (N : ℝ)) (hB : 0 ≤ B) (hσ : σ.CapLE B)
    (hτ : ∀ x, τ.w x ≤ 2 * (4 : ℝ) ^ (s + c) * σ.w x)
    (hshort : 2 * (4 : ℝ) ^ s * (8 : ℝ) ^ c * B ≤ Real.exp wS)
    (hw : wS ≤ w) : τ.WidthLE w := by
  intro x
  apply (le_div_iff₀ hN).2
  have hτN := mul_le_mul_of_nonneg_left (hτ x) hN.le
  have hσN := mul_le_mul_of_nonneg_left (hσ x) (show 0 ≤ 2 * (4 : ℝ) ^ (s + c) by positivity)
  have h4c : (4 : ℝ) ^ c ≤ (8 : ℝ) ^ c := pow_le_pow_left₀ (by norm_num) (by norm_num) c
  have hscale : 2 * (4 : ℝ) ^ (s + c) * B ≤ 2 * (4 : ℝ) ^ s * (8 : ℝ) ^ c * B := by
    rw [pow_add]
    convert mul_le_mul_of_nonneg_left h4c (show 0 ≤ 2 * (4 : ℝ) ^ s * B by positivity) using 1 <;> ring
  have hBexp := hscale.trans (hshort.trans (Real.exp_le_exp.2 hw))
  nlinarith [hτN, hσN]

/-- The actual pinned-label mass failure is bounded by the short crossing
tail plus a uniform tail for its normalized homogeneous bulk row. -/
theorem pinned_mass_from_exposure_tails {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (μ : Law (T.S.N k))
    (pins : Finset (Pos T k)) (hPins : pins ⊆ D.externalEarly v)
    (fixed : Pos T k → Fin (T.S.N k)) (Z : ℝ) (hZ : 7 / 8 ≤ Z)
    (hrow : ∀ x, Z * μ.w x = σ x * ∏ w ∈ pins, D.hitRatio w x (fixed w))
    (ε δ : ℝ) (hδ : 0 ≤ δ)
    (hCross : (unpinnedCrossingLaw D v pins).pr (fun ys =>
      finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys < 15 / 16) ≤ ε)
    (hBulk : ∀ (ys : CrossingEarly D v pins → Fin (T.S.N k)) (τ : Law (T.S.N k)),
      15 / 16 ≤ finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys →
      (∀ x, finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys * τ.w x =
        μ.w x * ∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w)) →
      (unpinnedBulkLaw D v pins).pr (fun zs =>
        finiteRowMass τ (fun w : BulkEarly D v pins => D.hitRatio w.1.1) zs < 2 / 3) ≤ δ) :
    (D.pinnedLabelLaw v pins fixed).pr (fun ys =>
      D.gateMassFailure v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤ ε + δ := by
  classical
  let U := UnpinnedEarly D v pins
  let p : U → Prop := fun w => D.G.patchOf w.1 ≠ D.G.patchOf v
  let P : U → FinLaw (Fin (T.S.N k)) := fun w =>
    ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))
  let f : CrossingEarly D v pins → Fin (T.S.N k) → Fin (T.S.N k) → ℝ :=
    fun w => D.hitRatio w.1.1
  let g : BulkEarly D v pins → Fin (T.S.N k) → Fin (T.S.N k) → ℝ :=
    fun w => D.hitRatio w.1.1
  rw [pinned_row_failure_reduction D v σ μ pins hPins fixed Z hrow]
  have hsub : (FinLaw.pi P).pr (fun zs =>
      Z * finiteRowMass μ (fun w : U => D.hitRatio w.1) zs < 1 / 2) ≤
      (FinLaw.pi P).pr (fun zs => finiteRowMass μ (fun w : U => D.hitRatio w.1) zs < 4 / 7) := by
    apply Lane_q_s17_pool.pr_mono
    intro zs hz
    by_contra hnot
    have hh := mul_le_mul hZ (le_of_not_gt hnot) (by norm_num : (0 : ℝ) ≤ 4 / 7) (by linarith : 0 ≤ Z)
    norm_num at hh
    linarith
  apply hsub.trans
  have hSplit (ys : CrossingEarly D v pins → Fin (T.S.N k))
      (zs : BulkEarly D v pins → Fin (T.S.N k)) :
      finiteRowMass μ (fun w : U => D.hitRatio w.1)
        (fun w => if h : p w then ys ⟨w, h⟩ else zs ⟨w, h⟩) =
      ∑ x, μ.w x * (∏ w : CrossingEarly D v pins, f w x (ys w)) *
        ∏ w : BulkEarly D v pins, g w x (zs w) := by
    unfold finiteRowMass
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Fintype.prod_subtype_mul_prod_subtype p]
    have hC : (∏ w : {w : U // p w}, D.hitRatio w.1.1 x
        (if h : p w.1 then ys ⟨w.1, h⟩ else zs ⟨w.1, h⟩)) =
        ∏ w : CrossingEarly D v pins, f w x (ys w) := by
      apply Fintype.prod_congr
      intro w
      simp [w.2, f]
    have hB : (∏ w : {w : U // ¬ p w}, D.hitRatio w.1.1 x
        (if h : p w.1 then ys ⟨w.1, h⟩ else zs ⟨w.1, h⟩)) =
        ∏ w : BulkEarly D v pins, g w x (zs w) := by
      apply Fintype.prod_congr
      intro w
      simp [w.2, g]
    rw [hC, hB]
    ring
  have hPartition : (FinLaw.pi P).pr (fun zs => finiteRowMass μ (fun w : U => D.hitRatio w.1) zs < 4 / 7) =
      (unpinnedCrossingLaw D v pins).E (fun ys => (unpinnedBulkLaw D v pins).pr (fun zs =>
        (∑ x, μ.w x * (∏ w, f w x (ys w)) * ∏ w, g w x (zs w)) < 4 / 7)) := by
    rw [pi_pr_partition P p]
    congr 1
    funext ys
    congr 1
    funext zs
    apply propext
    rw [hSplit ys zs]
  rw [hPartition]
  exact crossing_bulk_failure_bound (C := CrossingEarly D v pins) (B := BulkEarly D v pins)
    (α := Fin (T.S.N k)) (β := Fin (T.S.N k)) μ (unpinnedCrossingLaw D v pins) (unpinnedBulkLaw D v pins)
    f g (fun w x y => hitRatio_nonneg D _ _ _) ε δ hδ hCross hBulk

structure MassIndexBounds (κ : CConsts) (T : Stage) (k : ℕ) (K wS wL err : ℝ) : Prop where
  n_ge : 2 ≤ T.S.n k
  log_ge : 1 ≤ Real.log (T.S.n k : ℝ)
  err_nonneg : 0 ≤ err
  err_small : err ≤ bstar T k
  bstar_small : bstar T k ≤ 1 / 16
  pins_small : 6 * (ListGateContext.pinBudget κ : ℝ) * bstar T k ≤ 1 / 100
  crossing_small : 8 * K * Real.sqrt (Real.log (T.S.n k : ℝ)) * bstar T k ≤ 1 / 16
  short_room : (4 + 3 * (ListGateContext.pinBudget κ : ℝ) + 8 * K) *
    (1 + Real.log (T.S.n k : ℝ)) ≤ wS
  bulk_width : wS ≤ (T.S.n k : ℝ) ^ (κ.xs / 4)
  profile_width : K * Real.sqrt (Real.log (T.S.n k : ℝ)) + Real.log 11 ≤
    (T.S.n k : ℝ) ^ (κ.xs / 4)
  loss_small : (2 + K + 2 * κ.A0 + (ListGateContext.pinBudget κ : ℝ)) *
    (Real.log (T.S.n k : ℝ)) ^ 4 ≤ (T.S.n k : ℝ) / 2
  drift_small : K * Real.log (T.S.n k : ℝ) / T.S.n k ≤ bstar T k
  gamma_small : (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) < 1
  tail_sum : (T.S.n k : ℝ) * (2 * Real.exp
      (K * Real.sqrt (Real.log (T.S.n k : ℝ)) + Real.log 11 - wL)) +
    (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) *
      ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) +
        4 ^ (κ.u + 1) * (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ)))) ≤
    (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (-(2 * (κ.R : ℝ)))

/-- Choose one common index for the analytic width, drift, incidence and probability budgets. -/
theorem eventually_mass_index_bounds (κ : CConsts) (hκ : κ.Admissible)
    (T : Stage) (K : ℝ) (hK : 0 < K) :
    ∀ᶠ k in atTop, MassIndexBounds κ T k K
      ((T.S.n k : ℝ) ^ min κ.xι (κ.xs / 4))
      (κ.αι * T.S.n k) ((T.S.n k : ℝ) ^ (-1 + κ.ι / 2)) := by
  classical
  let r := min κ.xι (κ.xs / 4)
  let s₀ : ℝ := ListGateContext.pinBudget κ
  let Cwidth := 20 + 3 * s₀ + 8 * K
  let Closs := 2 + K + 2 * κ.A0 + s₀
  let Ctime := 2 * (K + Real.log 11 + 1) / κ.αι
  let Cbulk := (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) * (1 + (4 : ℝ) ^ (κ.u + 1))
  have hr : 0 < r := lt_min hκ.xι_pos (by linarith [hκ.xs_rng.1])
  have hαι : 0 < κ.αι := hκ.αι_pos
  have hs₀ : 0 ≤ s₀ := by dsimp [s₀]; positivity
  have hRnat : 0 < κ.R := by rw [hκ.R_eq]; exact Nat.pow_pos (by have := hκ.P_big.2; omega)
  have hR : 0 < (κ.R : ℝ) := by exact_mod_cast hRnat
  have hA0 : 0 ≤ κ.A0 := by nlinarith [hκ.A0_big]
  have hlog11 : 0 ≤ Real.log (11 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog11Bound : Real.log (11 : ℝ) ≤ 10 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
    linarith
  have hCwidth : 0 ≤ Cwidth := by dsimp [Cwidth]; positivity
  have hCloss : 0 ≤ Closs := by dsimp [Closs]; positivity
  have hCtime : 0 ≤ Ctime := by dsimp [Ctime]; positivity
  have hnT : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hlogT := Real.tendsto_log_atTop.comp hnT
  have hbT : Tendsto (fun k => bstar T k) atTop (nhds 0) := by
    unfold bstar
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 0.96)).comp hnT using 1
    ext k
    congr 1
    norm_num
  have hpinT : Tendsto (fun k => 6 * s₀ * bstar T k) atTop (nhds 0) := by
    simpa using hbT.const_mul (6 * s₀)
  have hgammaT : Tendsto (fun k => (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ)))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : 0 < 3 * (κ.R : ℝ))).comp hnT
  have hcrossT := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (2 * (κ.R : ℝ) + 1) (κ.αι / 2) (by linarith [hκ.αι_pos])).comp hnT
  have hbulkT : Tendsto (fun k => Cbulk * (T.S.n k : ℝ) ^ (-(κ.R : ℝ))) atTop (nhds 0) := by
    simpa using ((tendsto_rpow_neg_atTop hR).comp hnT).const_mul Cbulk
  have hroom := eventually_short_width_room T r Cwidth hr hCwidth
  have hdrift := eventually_short_width_room T 0.04 K (by norm_num) hK.le
  have hcrossRoom := eventually_short_width_room T 0.96 (128 * K) (by norm_num) (by positivity)
  have htimeRoom := eventually_short_width_room T 1 Ctime (by norm_num) hCtime
  have hloss := Lane_q_s17_pool.eventually_log4_small T Closs hCloss
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2, hlogT.eventually_ge_atTop (1 : ℝ),
    hroom, hdrift, hcrossRoom, htimeRoom, hloss,
    hbT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16)),
    hpinT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100)),
    hgammaT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hcrossT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    hbulkT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
    with k hn hy hroom hdrift hcrossRoom htimeRoom hloss hb hpin hgamma hcross hbulk
  let n : ℝ := T.S.n k
  let y := Real.log n
  let W := K * Real.sqrt y + Real.log 11
  have hn0 : 0 < n := by dsimp [n]; exact_mod_cast (by omega : 0 < T.S.n k)
  have hn1 : 1 ≤ n := by dsimp [n]; exact_mod_cast (by omega : 1 ≤ T.S.n k)
  have hy1 : 1 ≤ y := hy
  have hy0 : 0 ≤ y := by linarith
  have hsqrt : Real.sqrt y ≤ y := (Real.sqrt_le_left hy0).2 (by nlinarith)
  have hbstar : 0 ≤ bstar T k := by unfold bstar; positivity
  have hbEq : bstar T k = n ^ (-0.96 : ℝ) := by dsimp [bstar, n]; congr 1 <;> norm_num
  have hWidth : n ^ r ≤ n ^ (κ.xs / 4) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (min_le_right _ _)
  have hProfile : W ≤ n ^ (κ.xs / 4) := by
    apply le_trans _ hWidth
    apply le_trans _ hroom
    have hh := mul_le_mul_of_nonneg_left hsqrt hK.le
    dsimp [W, Cwidth]
    nlinarith
  have hTime : W ≤ κ.αι * n / 2 := by
    have ht := mul_le_mul_of_nonneg_left htimeRoom (show 0 ≤ κ.αι / 2 by positivity)
    have hID : κ.αι / 2 * (Ctime * (1 + y)) = (K + Real.log 11 + 1) * (1 + y) := by
      dsimp [Ctime]
      field_simp [hαι.ne'] <;> ring
    rw [hID] at ht
    simp only [Real.rpow_one] at ht
    have hh := mul_le_mul_of_nonneg_left hsqrt hK.le
    dsimp [W]
    nlinarith
  have hDrift : K * y / n ≤ bstar T k := by
    have hKy : K * y ≤ n ^ (0.04 : ℝ) := by
      apply le_trans _ hdrift
      nlinarith
    apply le_trans (div_le_div_of_nonneg_right hKy hn0.le)
    rw [hbEq]
    have hID : n ^ (0.04 : ℝ) / n = n ^ (-0.96 : ℝ) := by
      conv_lhs => rhs; rw [← Real.rpow_one n]
      rw [← Real.rpow_sub hn0]
      congr 1
      norm_num
    exact hID.le
  have hCrossSmall : 8 * K * Real.sqrt y * bstar T k ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_right hcrossRoom hbstar
    have hID : n ^ (0.96 : ℝ) * bstar T k = 1 := by
      rw [hbEq, ← Real.rpow_add hn0]
      norm_num
    rw [hID] at hh
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hK.le) hbstar
    nlinarith
  have hι : κ.ι ≤ 0.08 := by
    have hh := hκ.ι_rng.2
    have hm : min κ.xs (min κ.η0 0.01) ≤ 0.01 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hErr : n ^ (-1 + κ.ι / 2) ≤ bstar T k := by
    rw [hbEq]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hCrossProb : n * (2 * Real.exp (W - κ.αι * n)) ≤ (1 / 4 : ℝ) * n ^ (-(2 * (κ.R : ℝ))) := by
    rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hn0 _)).2
    have hcross' : n ^ (2 * (κ.R : ℝ) + 1) * Real.exp (-(κ.αι / 2) * n) ≤ 1 / 8 := hcross.le
    have hPow : n ^ (2 * (κ.R : ℝ) + 1) = n * n ^ (2 * (κ.R : ℝ)) := by
      conv_rhs => lhs; rw [← Real.rpow_one n]
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc
      _ ≤ n * (2 * Real.exp (-(κ.αι / 2) * n)) * n ^ (2 * (κ.R : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
        apply mul_le_mul_of_nonneg_left _ hn0.le
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        apply Real.exp_le_exp.2
        linarith
      _ = 2 * (n ^ (2 * (κ.R : ℝ) + 1) * Real.exp (-(κ.αι / 2) * n)) := by rw [hPow]; ring
      _ ≤ 1 / 4 := by nlinarith
  have hBulkProb : (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) *
      (n ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * n ^ (-(3 * (κ.R : ℝ)))) ≤
      (1 / 4 : ℝ) * n ^ (-(2 * (κ.R : ℝ))) := by
    have hbulk' : Cbulk * n ^ (-(κ.R : ℝ)) ≤ 1 / 4 := hbulk.le
    have hID : n ^ (-(κ.R : ℝ)) * n ^ (-(2 * (κ.R : ℝ))) = n ^ (-(3 * (κ.R : ℝ))) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc
      _ = Cbulk * n ^ (-(3 * (κ.R : ℝ))) := by dsimp [Cbulk]; ring
      _ = (Cbulk * n ^ (-(κ.R : ℝ))) * n ^ (-(2 * (κ.R : ℝ))) := by
        conv_rhs => rw [mul_assoc, hID]
      _ ≤ _ := mul_le_mul_of_nonneg_right hbulk' (Real.rpow_nonneg hn0.le _)
  refine {
    n_ge := hn
    log_ge := hy1
    err_nonneg := Real.rpow_nonneg hn0.le _
    err_small := hErr
    bstar_small := hb.le
    pins_small := hpin.le
    crossing_small := hCrossSmall
    short_room := ?_
    bulk_width := hWidth
    profile_width := hProfile
    loss_small := ?_
    drift_small := hDrift
    gamma_small := hgamma
    tail_sum := ?_ }
  · apply le_trans _ hroom
    dsimp [Cwidth, s₀]
    nlinarith
  · have hh : Closs * y ^ 4 ≤ n / 4 := hloss
    exact hh.trans (by linarith)
  · change n * (2 * Real.exp (W - κ.αι * n)) + _ ≤ _
    nlinarith [hCrossProb, hBulkProb]

/-- Fixed-index assembly of the actual independent retained-mass estimate. -/
theorem fixed_independent_mass {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (D : ListGateContext κ T k PT) (K : ℝ) (hK : 0 < K)
    (hq : D.L16QuantitativeValidity K) (v : Pos T k) (heven : IsEvenRole v)
    (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (pins : Finset (Pos T k)) (hPins : pins ⊆ D.externalEarly v)
    (fixed : Pos T k → Fin (T.S.N k)) (hs : pins.card ≤ ListGateContext.pinBudget κ)
    (hMass : (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤ D.pinnedPriorMass v σ pins fixed)
    (wS wL err : ℝ) (hDisc : TwoBudgetDisc T k wS wL err)
    (hIndex : MassIndexBounds κ T k K wS wL err) (q₀ : ℝ)
    (hq₀ : Real.log (((⌊(4 : ℝ) ^ (κ.u + 3) / κ.ξ ^ 2⌋₊).succ : ℕ) : ℝ) ≤ q₀ ∧ 1 ≤ q₀)
    (hGamma : ∀ (a : PT.mesh.V) (ha : a ∈ PT.activeVertices) (τ : Law (T.S.N k)) (s c d : ℕ),
      s ≤ ListGateContext.pinBudget κ → c ≤ (PT.tiling.P (D.G.patchOf v)).ℓ →
      d ≤ (D.externalEarly v).card → (T.S.n k : ℝ) / 2 ≤ d →
      (∀ x, τ.w x ≤ 2 * (4 : ℝ) ^ (s + c) * σ x) →
      Real.exp (Cstar κ.u κ.ξ * ((PT.tiling.Q (D.G.patchOf v) : ℝ) + q₀)) *
        (PT.mesh.corner a (D.G.patchOf v)).sup' (D.tiling_valid.corner_clean _ a ha).nonempty
          (fun x => τ.w x * Real.rpow (deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf v)).w x)
            (-(d : ℝ))) ≤ (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))))
    (hTail : ∀ H : S12.HomogeneousInput κ hκ T k PT.tiling.c 1,
      (FinLaw.pi fun _ : Fin H.S.d => ListGateContext.lawAsFinLaw H.π).pr
        (fun ys => productMass H.S.τ (fun _ x y => hit (T.S.E k) PT.tiling.c x y /
          deg (T.S.E k) PT.tiling.c H.π.w x) ys < 2 / 3) ≤
      (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) *
        ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * H.gamma)) :
    (D.pinnedLabelLaw v pins fixed).pr (fun ys =>
      D.gateMassFailure v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
      (1 / 2 : ℝ) * (T.S.n k : ℝ) ^ (-(2 * (κ.R : ℝ))) := by
  classical
  let i := D.G.patchOf v
  let y := Real.log (T.S.n k : ℝ)
  let c := Fintype.card (CrossingEarly D v pins)
  let d := Fintype.card (BulkEarly D v pins)
  let W := K * Real.sqrt y + Real.log 11
  let B := (2 : ℝ) ^ (PT.tiling.P i).h * (2 * Real.exp (K * Real.sqrt y))
  have hn : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by have := hIndex.n_ge; omega : 0 < T.S.n k)
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hbstar : 0 ≤ bstar T k := by unfold bstar; positivity
  have hA0 : 0 ≤ κ.A0 := by nlinarith [hκ.A0_big, (Nat.cast_nonneg κ.R : (0 : ℝ) ≤ κ.R)]
  obtain ⟨a, ha, hsupport, _, _⟩ := hσ.2.2
  let X := PT.mesh.corner a i
  have hXenv : X ⊆ PT.envelope i := by
    intro x hx
    rw [D.tiling_valid.envelope_eq]
    exact Finset.mem_biUnion.mpr ⟨a, ha, hx⟩
  have hX : X ⊆ T.X k := by
    intro x hx
    exact (Finset.mem_sdiff.mp ((D.tiling_valid.tiling_valid.patch_supports i).2.1
      ((D.tiling_valid.tiling_valid.patch_supports i).1
        (D.tiling_valid.envelope_subset i (hXenv hx))))).1
  have hDeg : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v,
      |deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x - 1 / 2| ≤ 3 * bstar T k := by
    intro x hx w hw
    have hh := Lane_q_s17_pool.cleanSupport_external_degree_drift D D.tiling_valid K
      hq.geometry v σ hσ hn x hx w hw
    apply hh.trans
    apply max_le _ le_rfl
    have hb := hIndex.drift_small
    linarith
  have hRatio : ∀ x, σ x ≠ 0 → ∀ w ∈ D.externalEarly v, ∀ z, D.hitRatio w x z ≤ 4 := by
    intro x hx w hw z
    have hd := (abs_le.mp (hDeg x hx w hw)).1
    have hquarter : 1 / 4 ≤ deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by
      linarith [hIndex.bstar_small]
    have hdpos : 0 < deg (T.S.E k) PT.tiling.c (PT.π (D.G.patchOf w)).w x := by linarith
    unfold ListGateContext.hitRatio
    apply (div_le_iff₀ hdpos).2
    have hhit : hit (T.S.E k) PT.tiling.c x z ≤ 1 := by unfold hit; split_ifs <;> norm_num
    nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hσcap := clean_prior_cap D v σ hσ (K * Real.sqrt y) (by positivity)
    (hq.geometry.mass_bound i) (low_mode_gain_budgets hκ D i).1
  obtain ⟨μ, Z, hZ, hμcap, hrow, hμdom⟩ := pin_row_mass_setup D v σ hσ pins hPins fixed
    (ListGateContext.pinBudget κ) hs hMass (3 * bstar T k) B (by positivity)
    (by linarith [hIndex.bstar_small]) (by nlinarith [hIndex.pins_small]) hB hσcap hDeg
  have hμX : μ.SupportedIn X := by
    intro x hx
    have hz : σ x = 0 := by by_contra hne; exact hx (hsupport x hne)
    have hh := hμdom x
    rw [hz, mul_zero] at hh
    exact le_antisymm hh (μ.nonneg x)
  obtain ⟨hc, hdExt, hdLow⟩ := unpinned_partition_counts D K hq v pins hs
  change c ≤ (PT.tiling.P i).ℓ at hc
  change d ≤ (D.externalEarly v).card at hdExt
  have hcR : (c : ℝ) ≤ K * Real.sqrt y :=
    (by exact_mod_cast hc : (c : ℝ) ≤ (PT.tiling.P i).ℓ).trans (hq.geometry.prefix_bound i)
  have hsqrt : Real.sqrt y ≤ y := (Real.sqrt_le_left (by linarith [hIndex.log_ge])).2
    (by have hy : 1 ≤ y := hIndex.log_ge; nlinarith)
  have hy : 1 ≤ y := hIndex.log_ge
  have hy4 : y ≤ y ^ 4 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hy : (1 : ℝ) ≤ y ^ 3) (by linarith : 0 ≤ y)
    convert hh using 1 <;> ring
  let loss := (PT.tiling.P i).h + (PT.tiling.P i).ℓ + D.G.r + ListGateContext.pinBudget κ
  have hLoss : (loss : ℝ) ≤ (T.S.n k : ℝ) / 2 := by
    have hh : ((PT.tiling.P i).h : ℝ) ≤ y ^ 4 := (hq.geometry.height_bound i).trans
      ((Real.rpow_le_rpow_of_exponent_le hy (by norm_num)).trans_eq (Real.rpow_natCast y 4))
    have hℓ := (hq.geometry.prefix_bound i).trans (mul_le_mul_of_nonneg_left hsqrt hK.le)
    have hr := hq.geometry.class_scale.2.le
    have hpin := mul_le_mul_of_nonneg_left (one_le_pow₀ hy : (1 : ℝ) ≤ y ^ 4)
      (Nat.cast_nonneg (ListGateContext.pinBudget κ))
    dsimp [loss]
    push_cast
    have hKi := mul_le_mul_of_nonneg_left hy4 hK.le
    have hAi := mul_le_mul_of_nonneg_left hy4 hA0
    have hLimit : (2 + K + 2 * κ.A0 + (ListGateContext.pinBudget κ : ℝ)) * y ^ 4 ≤
        (T.S.n k : ℝ) / 2 := hIndex.loss_small
    nlinarith
  have hLossNat : loss ≤ T.S.n k := by
    have hreal : (loss : ℝ) ≤ T.S.n k := by linarith
    exact_mod_cast hreal
  have hdLow' : T.S.n k - loss ≤ d := by
    simpa only [d, loss, i, BulkEarly, UnpinnedEarly, ← Nat.card_eq_fintype_card] using hdLow
  have hdHalf : (T.S.n k : ℝ) / 2 ≤ d := by
    have hcount : T.S.n k ≤ d + loss := by omega
    have hcountR : (T.S.n k : ℝ) ≤ (d : ℝ) + loss := by exact_mod_cast hcount
    linarith
  have hcN : c ≤ T.S.n k := by dsimp [loss] at hLossNat; omega
  have hd : d ≤ T.S.n k := hdExt.trans (Lane_q_s17_pool.externalEarly_card_le D v)
  have hShort : 2 * (4 : ℝ) ^ pins.card * (8 : ℝ) ^ c * B ≤ Real.exp wS :=
    short_restriction_cap_bound pins.card (ListGateContext.pinBudget κ) c (PT.tiling.P i).h K y wS
      hs hK.le hy hcR (hq.geometry.height_bound i) hIndex.short_room
  have hν : ∀ j, (PT.π j).WidthLE W := fun j =>
    Lane_q_s17_pool.profiled_law_width_of_mass_bound D.tiling_valid j K (hq.geometry.mass_bound j)
  have hπwidth : (PT.π i).WidthLE ((T.S.n k : ℝ) ^ (κ.xs / 4)) := by
    intro z
    exact (hν i z).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.2 hIndex.profile_width) hN.le)
  have hqRatio : 1 / 2 ≤ ((1 / 2 : ℝ) - err) / (1 / 2 + 3 * bstar T k) := by
    apply (le_div_iff₀ (show 0 < (1 / 2 : ℝ) + 3 * bstar T k by positivity)).2
    nlinarith [hIndex.err_small, hIndex.bstar_small]
  have hμcrossCap := pinned_cap_for_crossing μ B wS
    (((1 / 2 : ℝ) - err) / (1 / 2 + 3 * bstar T k)) hB hqRatio hμcap hShort
  let ε := (T.S.n k : ℝ) * (2 * Real.exp (W - wL))
  let δ := (1 - (2 / 3 : ℝ)) ^ (-(κ.u : ℝ)) *
    ((T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))) + 4 ^ (κ.u + 1) * (T.S.n k : ℝ) ^ (-(3 * (κ.R : ℝ))))
  have hCross : (unpinnedCrossingLaw D v pins).pr (fun ys =>
      finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys < 15 / 16) ≤ ε := by
    apply (unpinned_crossing_tail D v pins μ X hX hXenv hμX wS wL err W hDisc
      hIndex.err_nonneg hIndex.err_small hIndex.bstar_small
      (by have hh := mul_le_mul_of_nonneg_right hcR hbstar; nlinarith [hIndex.crossing_small]) hμcrossCap hν).trans
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcN) (by positivity)
  have hGate : ∀ x ∈ X, S12.DegGate (T.S.E k) PT.tiling.c (PT.π i).w 1 (bstar T k) x := by
    intro x hx
    have hDrift := hq.geometry.degree_drift i x (hXenv hx)
    have hDrift' : |deg (T.S.E k) PT.tiling.c (PT.π i).w x - 1 / 2| ≤ K * y / T.S.n k := by
      apply (le_div_iff₀ hn).2
      nlinarith [hDrift]
    simpa [S12.DegGate] using hDrift'.trans hIndex.drift_small
  have hPos : ∀ x ∈ X, 0 < deg (T.S.E k) PT.tiling.c (PT.π i).w x := by
    intro x hx
    have hh := (abs_le.mp (hGate x hx)).1
    simp only [S12.DegGate, one_mul] at hh
    linarith [hIndex.bstar_small]
  have hBulk : ∀ (ys : CrossingEarly D v pins → Fin (T.S.N k)) (τ : Law (T.S.N k)),
      15 / 16 ≤ finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys →
      (∀ x, finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys * τ.w x =
        μ.w x * ∏ w : CrossingEarly D v pins, D.hitRatio w.1.1 x (ys w)) →
      (unpinnedBulkLaw D v pins).pr (fun zs =>
        finiteRowMass τ (fun w : BulkEarly D v pins => D.hitRatio w.1.1) zs < 2 / 3) ≤ δ := by
    intro ys τ hZc hrowc
    have hτdom := post_crossing_domination D v σ hσ.1 μ τ pins hPins fixed ys Z
      (finiteRowMass μ (fun w : CrossingEarly D v pins => D.hitRatio w.1.1) ys) hZ hZc hrow hrowc hRatio
    have hτX : τ.SupportedIn X := by
      intro x hx
      have hz : σ x = 0 := by by_contra hne; exact hx (hsupport x hne)
      have hh := hτdom x
      rw [hz, mul_zero] at hh
      exact le_antisymm hh (τ.nonneg x)
    have hτwidth := retained_row_width (cleanPriorLaw D v σ hσ) τ B wS
      ((T.S.n k : ℝ) ^ (κ.xs / 4)) hN hB hσcap hτdom hShort hIndex.bulk_width
    exact unpinned_bulk_tail hκ D v pins a ha τ hd hτX hτwidth hπwidth hGate hPos q₀ hq₀
      (hGamma a ha τ pins.card c d hs hc hdExt hdHalf hτdom) hIndex.gamma_small hTail
  exact (pinned_mass_from_exposure_tails D v σ μ pins hPins fixed Z hZ hrow ε δ
    (by dsimp [δ]; positivity) hCross hBulk).trans hIndex.tail_sum

end HypercubeRamsey.Lane_sol_s17_pool
