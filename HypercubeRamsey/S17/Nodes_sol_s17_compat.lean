import HypercubeRamsey.S17.Nodes_sol_s17_pool_experiment
import HypercubeRamsey.S17.Nodes_sol_s17_pool_mass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 1000000

universe u

namespace HypercubeRamsey.Lane_sol_s17_compat

open Classical Filter
open scoped BigOperators
open Lane_sol_s17_pool S16.Lane_q_s16_comp2

/-- Pushforwards preserve event probabilities through their readout. -/
theorem map_pr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (A : β → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun x => A (f x)) := by
  have h := map_expect P f (fun y => if A y then (1 : ℝ) else 0)
  simpa [FinLaw.E, FinLaw.pr, mul_ite] using h

theorem map_id {α : Type*} [Fintype α] (P : FinLaw α) : FinLaw.map P id = P := by
  apply finLaw_ext
  intro x
  simp [FinLaw.map]

/-- The marginal at one coordinate of a finite product is its given law. -/
theorem pi_map_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i)) (j : I) :
    FinLaw.map (FinLaw.pi P) (fun s => s j) = P j := by
  apply finLaw_ext
  intro y
  rw [map_weight_eq_pr]
  let z := Function.update
    (Classical.choice (nonempty_of_finLaw (FinLaw.pi P))) j y
  have h := pi_pr_cylinder P {j} z
  simpa [z] using h

/-- Averaging a function of one coordinate uses exactly its marginal law. -/
theorem pi_E_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (j : I) (f : Ω j → ℝ) : (FinLaw.pi P).E (fun s => f (s j)) = (P j).E f := by
  let g : ∀ i, Ω i → ℝ := Function.update (fun _ _ => 1) j f
  have hg (s : ∀ i, Ω i) : (∏ i, g i (s i)) = f (s j) := by
    rw [Finset.prod_eq_single j]
    · simp [g]
    · intro i hi hij
      simp [g, Function.update_of_ne hij]
    · simp
  rw [show (fun s : ∀ i, Ω i => f (s j)) = (fun s => ∏ i, g i (s i)) by
    funext s; exact (hg s).symm, pi_expect_prod]
  rw [Finset.prod_eq_single j]
  · simp [g]
  · intro i hi hij
    simp [g, Function.update_of_ne hij, FinLaw.E, FinLaw.sum_one]
  · simp

/-- Conditioning one product coordinate by any predicate preserves all others. -/
theorem pi_condition_predicate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (j : I) (A : Ω j → Prop)
    (hA : 0 < ∑ y ∈ Finset.univ.filter A, (P j).w y)
    (hp : 0 < ∑ s ∈ Finset.univ.filter (fun s : ∀ i, Ω i => A (s j)),
      (FinLaw.pi P).w s) :
    FinLaw.cond (FinLaw.pi P) (Finset.univ.filter (fun s => A (s j))) hp =
      FinLaw.pi (Function.update P j (FinLaw.cond (P j) (Finset.univ.filter A) hA)) := by
  have hmass : (∑ s ∈ Finset.univ.filter (fun s : ∀ i, Ω i => A (s j)),
      (FinLaw.pi P).w s) = ∑ y ∈ Finset.univ.filter A, (P j).w y := by
    have h := congrArg (fun Q : FinLaw (Ω j) => Q.pr A) (pi_map_coordinate P j)
    rw [map_pr] at h
    simpa [FinLaw.pr, Finset.sum_filter] using h
  apply finLaw_ext
  intro s
  simp only [FinLaw.cond, hmass, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [FinLaw.pi]
  by_cases hs : A (s j)
  · simp only [hs, ite_true]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    have ho : (∏ i ∈ Finset.univ.erase j,
        (Function.update P j (FinLaw.cond (P j) (Finset.univ.filter A) hA) i).w (s i)) =
          ∏ i ∈ Finset.univ.erase j, (P i).w (s i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    simp only [FinLaw.cond, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    rw [ho, Function.update_self]
    simp only [FinLaw.cond, Finset.mem_filter, Finset.mem_univ, true_and, hs, ite_true]
    ring
  · simp only [hs, ite_false, zero_div]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hs]

/-- A fixed forced first hit may be followed by independent small-width hits. -/
theorem forced_first_hit_tail {T : Stage} {k s : ℕ} {wS wL err W : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL err) (c : Colour)
    (μ : Law (T.S.N k)) (y : Fin (T.S.N k))
    (ν : Fin s → Law (T.S.N k)) (hμ : μ.SupportedIn (T.X k))
    (he : 0 ≤ err) (heq : err < 1 / 2)
    (hcap : μ.CapLE (Real.exp wS * (1 / 2 - err) ^ (s + 1)))
    (hν : ∀ i, (ν i).SupportedIn (T.Y k)) (hνW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr (fun ys =>
      (∑ x, μ.w x * hit (T.S.E k) c x y * ∏ i, hit (T.S.E k) c x (ys i)) <
        (1 / 2 - err) ^ (s + 1)) ≤
      (if (∑ x, μ.w x * hit (T.S.E k) c x y) < 1 / 2 - err then 1 else 0) +
        (s : ℝ) * (2 * Real.exp (W - wL)) := by
  let q := (1 / 2 : ℝ) - err
  let Z := ∑ x, μ.w x * hit (T.S.E k) c x y
  have hq : 0 < q := by dsimp [q]; linarith
  have hf : ∀ x, 0 ≤ hit (T.S.E k) c x y := fun x => by
    unfold hit; split_ifs <;> norm_num
  have hf1 : ∀ x, hit (T.S.E k) c x y ≤ 1 := fun x => by
    unfold hit; split_ifs <;> norm_num
  by_cases hz : Z < q
  · simp only [show (∑ x, μ.w x * hit (T.S.E k) c x y) < 1 / 2 - err from hz,
      ite_true]
    have h : (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr
        (fun ys => (∑ x, μ.w x * hit (T.S.E k) c x y *
          ∏ i, hit (T.S.E k) c x (ys i)) < q ^ (s + 1)) ≤ 1 := by
      calc
        _ ≤ ∑ ys, (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).w ys := by
          apply Finset.sum_le_sum
          intro ys hys
          split_ifs <;> simp [FinLaw.nonneg]
        _ = 1 := FinLaw.sum_one _
    have hn : 0 ≤ (s : ℝ) * (2 * Real.exp (W - wL)) := by positivity
    exact h.trans (by linarith)
  · have hqZ : q ≤ Z := le_of_not_gt hz
    have hZ : 0 < Z := hq.trans_le hqZ
    let τ := Lane_q_s17_pool.reweightLaw μ (fun x => hit (T.S.E k) c x y) hf Z hZ rfl
    have hτ : τ.SupportedIn (T.X k) := by
      intro x hx
      simp [τ, Lane_q_s17_pool.reweightLaw, hμ x hx]
    have hτcap : τ.CapLE (Real.exp wS * q ^ s) := by
      simpa using reweight_cap_step μ (fun x => hit (T.S.E k) c x y) hf Z hZ rfl
        (Real.exp wS) q 1 (Real.exp_pos _).le hq (by norm_num) hqZ (by simpa [q] using hcap) hf1
    have ht := independent_hits_lower_tail hDisc c τ ν hτ hq he hτcap hν hνW
    simp only [show ¬ (∑ x, μ.w x * hit (T.S.E k) c x y) < 1 / 2 - err from hz,
      ite_false, zero_add]
    refine (Lane_q_s17_pool.pr_mono _ ?_).trans ht
    intro ys hy
    have hmass : (∑ x, μ.w x * hit (T.S.E k) c x y *
        ∏ i, hit (T.S.E k) c x (ys i)) =
        Z * productMass τ (fun _ x z => hit (T.S.E k) c x z) ys := by
      unfold productMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [τ, Lane_q_s17_pool.reweightLaw]
      field_simp
    rw [hmass] at hy
    by_contra hn
    have hn' : q ^ s ≤ productMass τ (fun _ x z => hit (T.S.E k) c x z) ys :=
      le_of_not_gt hn
    have hprod : q ^ (s + 1) ≤ Z * productMass τ (fun _ x z => hit (T.S.E k) c x z) ys := by
      rw [pow_succ]
      calc
        q ^ s * q ≤ q ^ s * Z := mul_le_mul_of_nonneg_left hqZ (pow_nonneg hq.le _)
        _ ≤ productMass τ (fun _ x z => hit (T.S.E k) c x z) ys * Z :=
          mul_le_mul_of_nonneg_right hn' hZ.le
        _ = _ := by ring
    exact (not_lt_of_ge hprod) hy


/-- Every label in a physical bin has a prescribed within-bin index. -/
theorem binIndexRead_surjective {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (B : Bin PT.tiling i) (y : Fin (T.S.N k)) (hy : y ∈ B.1) :
    ∃ j : Fin (PT.tiling.P i).d, binIndexRead hPT i B j = y := by
  let j := Fin.cast (hPT.tiling_valid.bins_card i B.1 B.2) (B.1.equivFin ⟨y, hy⟩)
  refine ⟨j, ?_⟩
  simp [binIndexRead, j]

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

/-- A witness prescribes one slot and one within-bin index at each selected member. -/
abbrev CompatibilityWitness (D : ListGateContext κ T k PT) (v : Pos T k) :=
  Σ pins : {p : Finset (Pos T k) // p ⊆ D.externalEarly v ∧ p.card ≤ ListGateContext.pinBudget κ},
    (∀ w : pins.1, Fin (D.G.nslot (D.G.cellOf w.1))) ×
    (∀ w : pins.1, Fin (PT.tiling.P (D.G.patchOf w.1)).d)

noncomputable instance witnessFintype (D : ListGateContext κ T k PT) (v : Pos T k) :
    Fintype (CompatibilityWitness D v) := inferInstanceAs (Fintype
      (Σ pins : {p : Finset (Pos T k) // p ⊆ D.externalEarly v ∧ p.card ≤ ListGateContext.pinBudget κ},
        (∀ w : pins.1, Fin (D.G.nslot (D.G.cellOf w.1))) ×
        (∀ w : pins.1, Fin (PT.tiling.P (D.G.patchOf w.1)).d)))

theorem bin_cast_val {i j : Fin PT.tiling.m} (h : i = j) (B : Bin PT.tiling i) :
    (cast (congrArg (Bin PT.tiling) h) B).1 = B.1 := by
  subst j
  rfl

noncomputable def witnessBin (D : ListGateContext κ T k PT)
    (pools : D.PoolAssignment) (w : Pos T k) (j : Fin (D.G.nslot (D.G.cellOf w))) :
    Bin PT.tiling (D.G.patchOf w) :=
  cast (by rw [D.G.cellOf_patch]) (pools (D.G.cellOf w) j)

noncomputable def witnessLabels (D : ListGateContext κ T k PT) (v : Pos T k)
    (a : CompatibilityWitness D v) (pools : D.PoolAssignment) :
    Pos T k → Fin (T.S.N k) := fun w =>
  if hw : w ∈ a.1.1 then
    binIndexRead D.tiling_valid (D.G.patchOf w)
      (witnessBin D pools w (a.2.1 ⟨w, hw⟩)) (a.2.2 ⟨w, hw⟩)
  else ⟨0, T.S.N_pos k⟩

noncomputable def witnessFailure (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (a : CompatibilityWitness D v) (pools : D.PoolAssignment) : Prop :=
  D.LocalPoolsTypical v pools ∧
    (∀ w : a.1.1, hQuant.sampler.permittedBin w.1
      (witnessBin D pools w.1 (a.2.1 w))) ∧
    Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) <
      (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
        D.pinnedStatePriorMass v s a.1.1 (witnessLabels D v a pools) <
          (9 / 10 : ℝ) * Real.rpow 2 (-(a.1.1.card : ℝ)))

/-- The original compatibility predicate has a finite slot/index witness cover. -/
theorem compatibility_witness_cover (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (pools : D.PoolAssignment) (hf : D.compatibilityFailure v pools) :
    ∃ a : CompatibilityWitness D v, witnessFailure D K hQuant v a pools := by
  obtain ⟨htyp, hbad⟩ := hf
  unfold ListGateContext.compatiblePool at hbad
  push_neg at hbad
  obtain ⟨pins, hext, hcard, fixed, hperm, hpr⟩ := hbad
  have hslots (w : pins) : ∃ j : Fin (D.G.nslot (D.G.cellOf w.1)),
      fixed w.1 ∈ (witnessBin D pools w.1 j).1 ∧
        hQuant.sampler.permittedBin w.1 (witnessBin D pools w.1 j) := by
    obtain ⟨j, hj, hp⟩ := (hQuant.sampler.permission_present
      (D.G.cellOf w.1) (pools (D.G.cellOf w.1)) w.1 rfl (fixed w.1)).mp (hperm w.1 w.2)
    exact ⟨j, by
      have hv := bin_cast_val (PT := PT) (D.G.cellOf_patch w.1) (pools (D.G.cellOf w.1) j)
      have hv' : (witnessBin D pools w.1 j).1 = (pools (D.G.cellOf w.1) j).1 := hv
      rw [hv']
      exact hj, hp⟩
  choose slots hmem hpermission using hslots
  have hindices (w : pins) : ∃ j : Fin (PT.tiling.P (D.G.patchOf w.1)).d,
      binIndexRead D.tiling_valid _ (witnessBin D pools w.1 (slots w)) j = fixed w.1 :=
    binIndexRead_surjective D.tiling_valid _ _ _ (hmem w)
  choose indices hindices using hindices
  let a : CompatibilityWitness D v := ⟨⟨pins, hext, hcard⟩, slots, indices⟩
  have hlabels (w : Pos T k) (hw : w ∈ pins) : witnessLabels D v a pools w = fixed w := by
    simp only [witnessLabels, show w ∈ a.1.1 from hw, dite_true]
    exact hindices ⟨w, hw⟩
  refine ⟨a, htyp, hpermission, ?_⟩
  have hmass (s : D.F.State (D.G.cellOf v)) :
      D.pinnedStatePriorMass v s pins (witnessLabels D v a pools) =
        D.pinnedStatePriorMass v s pins fixed := by
    unfold ListGateContext.pinnedStatePriorMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    exact Finset.prod_congr rfl (fun w hw => by rw [hlabels w hw])
  change Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) <
    (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
      D.pinnedStatePriorMass v s pins (witnessLabels D v a pools) <
        (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)))
  simpa only [hmass] using hpr

/-- A union over the concrete finite witnesses bounds compatibility failure. -/
theorem compatibility_witness_union (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (μ : FinLaw D.PoolAssignment) :
    μ.pr (D.compatibilityFailure v) ≤
      ∑ a : CompatibilityWitness D v, μ.pr (witnessFailure D K hQuant v a) := by
  exact (Lane_q_s17_pool.pr_mono μ
    (compatibility_witness_cover D K hQuant v)).trans (pr_exists_le_sum μ _)

abbrev OptionData {I : Type*} (α β : Type u) : Option I → Type u
  | none => α
  | some _ => β

instance optionDataFintype {I : Type*} {α β : Type u} [Fintype α] [Fintype β] :
    ∀ i : Option I, Fintype (OptionData α β i)
  | none => inferInstance
  | some _ => inferInstance

noncomputable def optionLaw {I : Type*} {α β : Type u} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : I → FinLaw β) : ∀ i : Option I, FinLaw (OptionData α β i)
  | none => P
  | some i => Q i

/-- Product expectations split into their own and external coordinates. -/
theorem pi_option_expect {I : Type*} {α β : Type u}
    [Fintype I] [DecidableEq I] [DecidableEq (Option I)] [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : I → FinLaw β) (f : α → (I → β) → ℝ) :
    (FinLaw.pi (optionLaw P Q)).E (fun z => f (z none) (fun i => z (some i))) =
        P.E (fun x => (FinLaw.pi Q).E (f x)) := by
  let e := Equiv.piOptionEquivProd (β := OptionData (I := I) α β)
  unfold FinLaw.E
  have he := Fintype.sum_equiv e
    (fun z => (FinLaw.pi (optionLaw P Q)).w z * f (z none) (fun i => z (some i)))
    (fun p => (FinLaw.pi (optionLaw P Q)).w (e.symm p) *
      f ((e.symm p) none) (fun i => (e.symm p) (some i))) (fun z => by simp)
  rw [he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  simp [FinLaw.pi, Fintype.prod_option, e, optionLaw, mul_assoc]

/-- In the low modes, the physical bin size is at most the cube dimension. -/
theorem low_bin_size_le (D : ListGateContext κ T k PT) (hκ : κ.Admissible)
    (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) (hn : 1 ≤ T.S.n k)
    (i : Fin PT.tiling.m) : (PT.tiling.P i).d ≤ T.S.n k := by
  have htv := D.tiling_valid.tiling_valid
  cases hm : PT.tiling.mode with
  | bounded => simpa [(htv.bounded_data hm).2 i |>.2.2.1] using hn
  | lowDirect => simpa [(htv.direct_data (Or.inl hm) i).2.2.2.2.2.1] using hn
  | highDirect => simpa [hm, Mode.isLow] using D.mode_low
  | highSmall => simpa [hm, Mode.isLow] using D.mode_low
  | highLarge => simpa [hm, Mode.isLow] using D.mode_low
  | lowCluster =>
    have hc := htv.cluster_data (Or.inl hm) i
    have hd := hc.2.2.2.2.1 (Or.inl hm)
    have hq := (hc.2.2.2.2.2.2.2.2.2.1).mp hm
    have hM : 1 < (κ.Mlo : ℝ) := by
      have hh := hκ.Mlo_big
      have hcb : 0 < κ.Cb := by
        have hpos : 0 < 100 * κ.aC / κ.aB :=
          div_pos (mul_pos (by norm_num) hκ.aC_rng.1) hκ.aB_rng.1
        linarith [hκ.Cb_big]
      nlinarith
    have hcq : κ.cq ≤ 1 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 20 * (κ.Mlo : ℝ))).mp hκ.cq_rng.2
      nlinarith [hκ.cq_rng.1]
    have hpow : Real.rpow (Real.log (T.S.n k : ℝ)) κ.cq ≤ Real.log (T.S.n k : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hlog hcq
    have hqn : (PT.tiling.P i).q / 2 ≤ Real.log (T.S.n k : ℝ) := by
      nlinarith [hq.trans hpow]
    have hexp : Real.exp ((PT.tiling.P i).q / 2) ≤ (T.S.n k : ℝ) := by
      have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
      simpa [Real.exp_log hnpos] using Real.exp_le_exp.mpr hqn
    rw [hd]
    exact_mod_cast (Nat.floor_le (Real.exp_pos _).le).trans hexp

/-- Prescribing an in-bin index costs only logarithmic width in every low mode. -/
theorem low_bin_index_width (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K)
    (hκ : κ.Admissible) (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) (hn : 1 ≤ T.S.n k)
    (i : Fin PT.tiling.m) (j : Fin (PT.tiling.P i).d) :
    (binIndexLaw D.tiling_valid i j).WidthLE ((K + 1) * Real.log (T.S.n k : ℝ)) := by
  have hM : 0 < ((PT.tiling.P i).M : ℝ) := by
    have hnat : 0 < (PT.tiling.P i).M := by
      rw [← (PT.tiling.P i).cardX]
      exact Finset.card_pos.mpr (D.tiling_valid.tiling_valid.patch_nonempty i).1
    exact_mod_cast hnat
  have hb : 0 < (Fintype.card (Bin PT.tiling i) : ℝ) := by
    have h := bins_count_mul_size D.tiling_valid i
    have h' : 0 < (PT.tiling.P i).M := by exact_mod_cast hM
    exact_mod_cast (by nlinarith : 0 < Fintype.card (Bin PT.tiling i))
  have hd : 0 < ((PT.tiling.P i).d : ℝ) := by
    have hnat := bins_count_mul_size D.tiling_valid i
    have hMnat : 0 < (PT.tiling.P i).M := by exact_mod_cast hM
    exact_mod_cast (show 0 < (PT.tiling.P i).d by nlinarith)
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hcount : (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.tiling.P i).d =
      (PT.tiling.P i).M := by exact_mod_cast bins_count_mul_size D.tiling_valid i
  have hratio : (T.S.N k : ℝ) / Fintype.card (Bin PT.tiling i) =
      (T.S.N k : ℝ) / (PT.tiling.P i).M * (PT.tiling.P i).d := by
    rw [← hcount]; field_simp
  have hsqrt : Real.sqrt (Real.log (T.S.n k : ℝ)) ≤ Real.log (T.S.n k : ℝ) := by
    exact (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hwidth : Real.log ((T.S.N k : ℝ) / Fintype.card (Bin PT.tiling i)) ≤
      (K + 1) * Real.log (T.S.n k : ℝ) := by
    rw [hratio, Real.log_mul (div_pos hN hM).ne' hd.ne']
    have hdn : ((PT.tiling.P i).d : ℝ) ≤ T.S.n k := by
      exact_mod_cast low_bin_size_le D hκ hlog hn i
    have hld := Real.log_le_log hd hdn
    have hmass := (hQuant.geometry.mass_bound i).trans
      (mul_le_mul_of_nonneg_left hsqrt hK)
    nlinarith
  intro y
  exact (binIndexLaw_width D.tiling_valid i j y).trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hwidth) hN.le)


/-- Physical bins are nonempty in every valid patch. -/
theorem physical_bins_nonempty (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m) :
    (Finset.univ : Finset (Bin PT.tiling i)).Nonempty := by
  obtain ⟨y, hy⟩ := (D.tiling_valid.tiling_valid.patch_nonempty i).2
  obtain ⟨B, hB, _⟩ := (PT.tiling.P i).bins.exists_mem hy
  exact ⟨⟨B, hB⟩, Finset.mem_univ _⟩

noncomputable def uniformBin (D : ListGateContext κ T k PT) (i : Fin PT.tiling.m) :
    FinLaw (Bin PT.tiling i) := FinLaw.uniform Finset.univ (physical_bins_nonempty D i)

noncomputable def uniformCell (D : ListGateContext κ T k PT) (C : D.G.Cell) :
    FinLaw (CellPool D.G C) := FinLaw.pi fun _ => uniformBin D (D.G.cellPatch C)

/-- The actual iid assignment is the product of the physical slot laws. -/
theorem iidPoolLaw_eq_pi (D : ListGateContext κ T k PT)
    (hp : (permPools D.G).Nonempty) :
    iidPoolLaw D.G hp = FinLaw.pi (uniformCell D) := by
  apply finLaw_ext
  intro pools
  simp only [iidPoolLaw, uniformCell, uniformBin, FinLaw.uniform, FinLaw.pi,
    Finset.mem_univ, ite_true, Finset.card_univ]
  rw [Fintype.card_pi]
  push_cast
  rw [one_div, ← Finset.prod_inv_distrib]
  congr 1
  funext C
  rw [Fintype.card_pi]
  push_cast
  simp [one_div, Finset.prod_inv_distrib]

/-- The conditioning event for one physical slot has positive probability. -/
theorem uniformCell_pin_pos (D : ListGateContext κ T k PT) (p : D.PoolPin) :
    0 < ∑ P ∈ Finset.univ.filter (fun P : CellPool D.G p.cell => P p.slot = p.bin),
      (uniformCell D p.cell).w P := by
  have h := congrArg (fun Q => Q.w p.bin)
    (pi_map_coordinate (fun _ => uniformBin D (D.G.cellPatch p.cell)) p.slot)
  have hmass : (∑ P ∈ Finset.univ.filter (fun P : CellPool D.G p.cell => P p.slot = p.bin),
      (uniformCell D p.cell).w P) = (uniformBin D (D.G.cellPatch p.cell)).w p.bin := by
    simpa [FinLaw.map, Finset.sum_filter, uniformCell] using h
  rw [hmass]
  simp only [uniformBin, FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ]
  apply one_div_pos.mpr
  exact_mod_cast (Finset.card_pos.mpr (physical_bins_nonempty D _))

noncomputable def pinnedCell (D : ListGateContext κ T k PT) (p : D.PoolPin) :
    FinLaw (CellPool D.G p.cell) :=
  FinLaw.cond (uniformCell D p.cell)
    (Finset.univ.filter (fun P => P p.slot = p.bin)) (uniformCell_pin_pos D p)

noncomputable def cellLaws (D : ListGateContext κ T k PT) (p : Option D.PoolPin)
    (C : D.G.Cell) : FinLaw (CellPool D.G C) :=
  match p with
  | none => uniformCell D C
  | some p => Function.update (uniformCell D) p.cell (pinnedCell D p) C

/-- One global iid pin changes exactly one cell marginal. -/
theorem pinned_iidPoolLaw_eq_pi (D : ListGateContext κ T k PT)
    (hp : (permPools D.G).Nonempty) (p : D.PoolPin)
    (hpin : 0 < ∑ pools ∈ D.poolPinSet p, (iidPoolLaw D.G hp).w pools) :
    FinLaw.cond (iidPoolLaw D.G hp) (D.poolPinSet p) hpin =
      FinLaw.pi (cellLaws D (some p)) := by
  simp only [iidPoolLaw_eq_pi D hp] at hpin ⊢
  exact pi_condition_predicate (uniformCell D) p.cell
    (fun P => P p.slot = p.bin) (uniformCell_pin_pos D p) hpin

/-- A pin in a cell changes only the prescribed physical slot. -/
theorem pinnedCell_eq_pi (D : ListGateContext κ T k PT) (p : D.PoolPin) :
    pinnedCell D p = FinLaw.pi (fun j =>
      if j = p.slot then FinLaw.dirac p.bin else uniformBin D (D.G.cellPatch p.cell)) := by
  have h := pi_condition_coordinate (fun _ => uniformBin D (D.G.cellPatch p.cell))
    p.slot p.bin (uniformCell_pin_pos D p)
  refine h.trans ?_
  apply finLaw_ext
  intro P
  simp only [FinLaw.pi]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases he : j = p.slot
  · subst j
    simp
  · simp [he]

/-- Every unforced selected slot in a pinned cell is still a uniform physical bin. -/
theorem pinnedCell_unforced_marginal (D : ListGateContext κ T k PT) (p : D.PoolPin)
    (j : Fin (D.G.nslot p.cell)) (hj : j ≠ p.slot) :
    FinLaw.map (pinnedCell D p) (fun P => P j) = uniformBin D (D.G.cellPatch p.cell) := by
  rw [pinnedCell_eq_pi, pi_map_coordinate]
  simp [hj]

theorem pinnedCell_forced_marginal (D : ListGateContext κ T k PT) (p : D.PoolPin) :
    FinLaw.map (pinnedCell D p) (fun P => P p.slot) = FinLaw.dirac p.bin := by
  rw [pinnedCell_eq_pi, pi_map_coordinate]
  simp


/-- Reindexing independent coordinates gives the same product experiment. -/
theorem pi_reindex_pr {I J α : Type*} [Fintype I] [Fintype J] [Fintype α]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (P : J → FinLaw α) (A : (I → α) → Prop) :
    (FinLaw.pi P).pr (fun ys => A (fun i => ys (e i))) =
      (FinLaw.pi (fun i => P (e i))).pr A := by
  let q : (J → α) ≃ (I → α) := Equiv.arrowCongr e.symm (Equiv.refl α)
  unfold FinLaw.pr
  apply Fintype.sum_equiv q
  intro ys
  have hp : (∏ i : J, (P i).w (ys i)) = ∏ i : I, (P (e i)).w (ys (e i)) :=
    (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  simpa [q, Equiv.arrowCongr, FinLaw.pi, Function.comp_def] using congrArg
    (fun w : ℝ => if A (fun i => ys (e i)) then w else 0) hp

/-- The adaptive estimate also applies to any finite witness index type. -/
theorem independent_pin_mass_tail_fintype {I : Type*} [Fintype I] [DecidableEq I]
    {T : Stage} {k : ℕ} {wS wL err W : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL err) (c : Colour)
    (μ : Law (T.S.N k)) (ν : I → Law (T.S.N k))
    (hμ : μ.SupportedIn (T.X k)) (he : 0 ≤ err) (heSmall : err ≤ 1 / 4)
    (hs : 2 * (Fintype.card I : ℝ) * err ≤ 1 / 10)
    (hCap : μ.CapLE (Real.exp wS * (1 / 2 - err) ^ Fintype.card I))
    (hν : ∀ i, (ν i).SupportedIn (T.Y k)) (hνW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr (fun ys =>
      (∑ x, μ.w x * ∏ i, hit (T.S.E k) c x (ys i)) <
        (9 / 10 : ℝ) * Real.rpow 2 (-(Fintype.card I : ℝ))) ≤
      (Fintype.card I : ℝ) * (2 * Real.exp (W - wL)) := by
  letI : DecidableEq (Fin (Fintype.card I)) := instDecidableEqFin _
  let e := (Fintype.equivFin I).symm
  have hprod (ys : I → Fin (T.S.N k)) (x : Fin (T.S.N k)) :
      (∏ i : Fin (Fintype.card I), hit (T.S.E k) c x (ys (e i))) =
        ∏ i : I, hit (T.S.E k) c x (ys i) :=
    Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hp := pi_reindex_pr e (fun i => ListGateContext.lawAsFinLaw (ν i))
    (fun ys => productMass μ (fun _ x z => hit (T.S.E k) c x z) ys <
      (9 / 10 : ℝ) * Real.rpow 2 (-(Fintype.card I : ℝ)))
  simp only [productMass, hprod] at hp
  rw [hp]
  simpa only [productMass] using independent_pin_mass_tail hDisc c μ (fun i => ν (e i)) hμ he heSmall hs hCap
    (fun i => hν (e i)) (fun i => hνW (e i))

/-- The permission estimate can be stated directly on the unforced own-cell law. -/
theorem forced_permission_average_cell (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K)
    (v : Pos T k) (heven : IsEvenRole v) (b : Pos T k) (hb : b ∈ D.externalEarly v)
    (B : Bin PT.tiling (D.G.patchOf b)) (hB : hQuant.sampler.permittedBin b B)
    (y : Fin (T.S.N k)) (hy : y ∈ B.1) :
    (uniformCell D (D.G.cellOf v)).E (fun P =>
      if D.F.typical (D.G.cellOf v) P then
        (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
          |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
            2 * bstar T k) else 0) ≤ K * Real.exp (-κ.cperm * T.S.n k) := by
  have ht := forced_permission_average D K hK hQuant v heven b hb B hB y hy
  rw [iidPoolLaw_eq_pi] at ht
  let f : CellPool D.G (D.G.cellOf v) → ℝ := fun P =>
    if D.F.typical (D.G.cellOf v) P then
      (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
        |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
          2 * bstar T k) else 0
  have hm := pi_E_coordinate (uniformCell D) (D.G.cellOf v) f
  exact hm ▸ ht


noncomputable def selectedLabel (D : ListGateContext κ T k PT) (w : Pos T k)
    (j : Fin (D.G.nslot (D.G.cellOf w))) (l : Fin (PT.tiling.P (D.G.patchOf w)).d)
    (P : CellPool D.G (D.G.cellOf w)) : Fin (T.S.N k) :=
  binIndexRead D.tiling_valid (D.G.patchOf w)
    (cast (by rw [D.G.cellOf_patch]) (P j)) l

noncomputable def witnessAverage (D : ListGateContext κ T k PT) (v : Pos T k)
    (a : CompatibilityWitness D v) (pools : D.PoolAssignment) : ℝ :=
  if D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) then
    (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
      D.pinnedStatePriorMass v s a.1.1 (witnessLabels D v a pools) <
        (9 / 10 : ℝ) * Real.rpow 2 (-(a.1.1.card : ℝ)))
  else 0

noncomputable def selectedBadProbability (D : ListGateContext κ T k PT)
    (v : Pos T k) (pins : Finset (Pos T k))
    (P : CellPool D.G (D.G.cellOf v)) (ys : pins → Fin (T.S.N k)) : ℝ :=
  (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
    (∑ x, D.F.prior (D.G.cellOf v) s v x *
      ∏ w : pins, hit (T.S.E k) PT.tiling.c x (ys w)) <
        (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)))

/-- The joint own-pool/selected-label experiment uses independent cell marginals. -/
theorem witnessAverage_pi (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (a : CompatibilityWitness D v)
    (P : ∀ C, FinLaw (CellPool D.G C)) :
    (FinLaw.pi P).E (witnessAverage D v a) =
      (P (D.G.cellOf v)).E (fun own =>
        if D.F.typical (D.G.cellOf v) own then
          (FinLaw.pi fun w : a.1.1 =>
            FinLaw.map (P (D.G.cellOf w.1)) (selectedLabel D w.1 (a.2.1 w) (a.2.2 w))).E
              (selectedBadProbability D v a.1.1 own) else 0) := by
  letI : DecidableEq (Option a.1.1) := Classical.decEq _
  let e : Option a.1.1 → D.G.Cell := fun z =>
    match z with | none => D.G.cellOf v | some w => D.G.cellOf w.1
  have he : Function.Injective e := by
    intro i j hij
    obtain ⟨hown, hdistinct⟩ := hQuant.geometry.star_distinct v heven
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some w => exact False.elim (hown _ (a.1.2.1 w.2) hij.symm)
    | some w =>
      cases j with
      | none => exact False.elim (hown _ (a.1.2.1 w.2) hij)
      | some z =>
        congr 1
        exact Subtype.ext (hdistinct _ (a.1.2.1 w.2) _ (a.1.2.1 z.2) hij)
  let β : Option a.1.1 → Type := OptionData (CellPool D.G (D.G.cellOf v)) (Fin (T.S.N k))
  letI : ∀ z, Fintype (β z) := optionDataFintype
  let read : ∀ z, CellPool D.G (e z) → β z := fun z =>
    match z with | none => id | some w => selectedLabel D w.1 (a.2.1 w) (a.2.2 w)
  let f : (∀ z, β z) → ℝ := fun z =>
    if D.F.typical (D.G.cellOf v) (z none) then
      selectedBadProbability D v a.1.1 (z none) (fun w => z (some w)) else 0
  have hf (pools : D.PoolAssignment) : witnessAverage D v a pools =
      f (fun z => read z (pools (e z))) := by
    unfold witnessAverage
    dsimp [f, e, read]
    split_ifs <;> try rfl
    unfold selectedBadProbability
    congr 1
    funext s
    unfold ListGateContext.pinnedStatePriorMass
    have hmass : (∑ x, D.F.prior (D.G.cellOf v) s v x *
      ∏ w ∈ a.1.1, hit (T.S.E k) PT.tiling.c x (witnessLabels D v a pools w)) =
      ∑ x, D.F.prior (D.G.cellOf v) s v x *
        ∏ w : a.1.1, hit (T.S.E k) PT.tiling.c x
          (selectedLabel D w.1 (a.2.1 w) (a.2.2 w) (pools (D.G.cellOf w.1))) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      rw [← Finset.prod_attach]
      apply Finset.prod_congr rfl
      intro w hw
      simp [witnessLabels, selectedLabel, witnessBin, w.2]
    exact propext (by rw [hmass]; simp only [Real.rpow_eq_pow])
  change (FinLaw.pi P).E (fun pools => witnessAverage D v a pools) = _
  simp_rw [hf]
  rw [pi_E_injective_readouts P e he read f]
  have hl : (fun z => FinLaw.map (P (e z)) (read z)) =
      (fun z : Option a.1.1 => match z with
        | none => P (D.G.cellOf v)
        | some w => FinLaw.map (P (D.G.cellOf w.1)) (selectedLabel D w.1 (a.2.1 w) (a.2.2 w))) := by
    funext z
    cases z with
    | none => simpa only [e, read] using map_id (P (D.G.cellOf v))
    | some w =>
      apply finLaw_ext
      intro y
      simp [FinLaw.map, e, read]
  rw [hl]
  have ho := pi_option_expect (P (D.G.cellOf v))
    (fun w : a.1.1 => FinLaw.map (P (D.G.cellOf w.1)) (selectedLabel D w.1 (a.2.1 w) (a.2.2 w)))
    (fun own ys => if D.F.typical (D.G.cellOf v) own then
      selectedBadProbability D v a.1.1 own ys else 0)
  have hh : (FinLaw.pi (fun z : Option a.1.1 => match z with
    | none => P (D.G.cellOf v)
    | some w => FinLaw.map (P (D.G.cellOf w.1)) (selectedLabel D w.1 (a.2.1 w) (a.2.2 w)))).E f =
      (P (D.G.cellOf v)).E (fun own =>
        (FinLaw.pi fun w : a.1.1 => FinLaw.map (P (D.G.cellOf w.1))
          (selectedLabel D w.1 (a.2.1 w) (a.2.2 w))).E
            (fun ys => if D.F.typical (D.G.cellOf v) own then
              selectedBadProbability D v a.1.1 own ys else 0)) := by
    convert ho using 1 <;> congr!
    all_goals first | rfl | exact Subsingleton.elim _ _ |
      (rename_i z; cases z <;> rfl)
  refine hh.trans ?_
  apply congrArg (FinLaw.E _)
  funext own
  split_ifs with ht
  · rfl
  · simp [FinLaw.E]


/-- All valid initial priors have a common logarithmic cap for compatibility. -/
theorem clean_prior_log_cap (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K)
    (hκ : κ.Admissible) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ) :
    (cleanPriorLaw D v σ hσ).CapLE
      (Real.exp (Real.log 2 + (K + 1) * Real.log (T.S.n k : ℝ))) := by
  let y := Real.log (T.S.n k : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hsqrt : Real.sqrt y ≤ y := (Real.sqrt_le_left hy).mpr (by nlinarith [hlog])
  have hh : ((PT.tiling.P (D.G.patchOf v)).h : ℝ) ≤ y := by
    exact (hQuant.geometry.height_bound _).trans
      (by simpa using Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (1 / 10 : ℝ) ≤ 1))
  have ha : 0 ≤ κ.a := by rw [hκ.a_eq]; exact div_nonneg hκ.θ_rng.1.le (by norm_num)
  have hgain : 0 ≤ PT.tiling.gain (D.G.patchOf v) := by
    cases hm : PT.tiling.mode <;> simp only [Tiling.gain, hm] <;> positivity
  have hmass := (hQuant.geometry.mass_bound (D.G.patchOf v)).trans
    (mul_le_mul_of_nonneg_left hsqrt hK)
  have hcap := clean_prior_cap D v σ hσ (K * y) (mul_nonneg hK hy) hmass hgain
  have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have he : (PT.tiling.P (D.G.patchOf v)).h * Real.log 2 + Real.log 2 + K * y ≤
      Real.log 2 + (K + 1) * y := by
    have hh' := mul_le_mul_of_nonneg_left hh (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    have hy' := mul_le_mul_of_nonneg_right hlog2 hy
    nlinarith
  have hid : (2 : ℝ) ^ (PT.tiling.P (D.G.patchOf v)).h * (2 * Real.exp (K * y)) =
      Real.exp ((PT.tiling.P (D.G.patchOf v)).h * Real.log 2 + Real.log 2 + K * y) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    ring
  intro x
  exact (hcap x).trans (by rw [hid]; exact Real.exp_le_exp.mpr he)

/-- The cap budget absorbs every short successful restriction uniformly. -/
theorem clean_prior_short_cap (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K)
    (hκ : κ.Admissible) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (err : ℝ) (he : 0 ≤ err) (heSmall : err ≤ 1 / 4)
    (hRoom : Real.log 2 + (ListGateContext.pinBudget κ : ℝ) * Real.log 4 +
      (K + 1) * Real.log (T.S.n k : ℝ) ≤ Real.rpow (T.S.n k : ℝ) κ.xs)
    (v : Pos T k) (σ : Fin (T.S.N k) → ℝ) (hσ : D.CleanInitialPrior v σ)
    (s : ℕ) (hs : s ≤ ListGateContext.pinBudget κ) :
    (cleanPriorLaw D v σ hσ).CapLE
      (Real.exp (Real.rpow (T.S.n k : ℝ) κ.xs) * (1 / 2 - err) ^ s) := by
  let B := ListGateContext.pinBudget κ
  let w := Real.rpow (T.S.n k : ℝ) κ.xs
  have hq : (1 / 4 : ℝ) ≤ 1 / 2 - err := by linarith
  have hq1 : (1 / 2 : ℝ) - err ≤ 1 := by linarith
  have hpower : (1 / 4 : ℝ) ^ B ≤ (1 / 2 - err) ^ s := by
    calc
      _ ≤ (1 / 4 : ℝ) ^ s := pow_right_anti₀ (by norm_num) (by norm_num) hs
      _ ≤ (1 / 2 - err) ^ s := pow_le_pow_left₀ (by norm_num) hq _
  have hfour : (1 / 4 : ℝ) ^ B = Real.exp (-(B : ℝ) * Real.log 4) := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp [one_div, inv_pow]
  have hbound : Real.exp (Real.log 2 + (K + 1) * Real.log (T.S.n k : ℝ)) ≤
      Real.exp w * (1 / 4 : ℝ) ^ B := by
    rw [hfour, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [w, B]
    simp only [Real.rpow_eq_pow] at hRoom
    linarith
  intro x
  exact (clean_prior_log_cap D K hK hQuant hκ hlog v σ hσ x).trans
    (hbound.trans (mul_le_mul_of_nonneg_left hpower (Real.exp_pos _).le))


/-- Composing finite pushforwards composes their deterministic readouts. -/
theorem map_comp {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ]
    (P : FinLaw α) (f : α → β) (g : β → γ) :
    FinLaw.map (FinLaw.map P f) g = FinLaw.map P (fun x => g (f x)) := by
  apply finLaw_ext
  intro z
  rw [map_weight_eq_pr, map_pr, map_weight_eq_pr]

/-- The physical uniform-bin law induces exactly the prescribed index law. -/
theorem uniformBin_index_marginal (D : ListGateContext κ T k PT)
    {i i' : Fin PT.tiling.m} (h : i = i') (l : Fin (PT.tiling.P i').d) :
    FinLaw.map (uniformBin D i) (fun B =>
      binIndexRead D.tiling_valid i' (cast (congrArg (Bin PT.tiling) h) B) l) =
        ListGateContext.lawAsFinLaw (binIndexLaw D.tiling_valid i' l) := by
  subst i'
  apply finLaw_ext
  intro y
  simp [uniformBin, binIndexLaw, ListGateContext.lawAsFinLaw, FinLaw.map, FinLaw.uniform]

/-- A selected unforced physical slot has exactly the small-width index law. -/
theorem uniformCell_selected_marginal (D : ListGateContext κ T k PT)
    (w : Pos T k) (j : Fin (D.G.nslot (D.G.cellOf w)))
    (l : Fin (PT.tiling.P (D.G.patchOf w)).d) :
    FinLaw.map (uniformCell D (D.G.cellOf w)) (selectedLabel D w j l) =
      ListGateContext.lawAsFinLaw (binIndexLaw D.tiling_valid (D.G.patchOf w) l) := by
  apply finLaw_ext
  intro y
  rw [map_weight_eq_pr]
  let f : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w)) → Fin (T.S.N k) := fun B =>
    binIndexRead D.tiling_valid (D.G.patchOf w)
      (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch w)) B) l
  have hc := pi_E_coordinate
    (fun _ : Fin (D.G.nslot (D.G.cellOf w)) => uniformBin D (D.G.cellPatch (D.G.cellOf w))) j
    (fun B => if f B = y then (1 : ℝ) else 0)
  have hpr : (uniformCell D (D.G.cellOf w)).pr (fun P => selectedLabel D w j l P = y) =
      (uniformBin D (D.G.cellPatch (D.G.cellOf w))).pr (fun B => f B = y) := by
    calc
      _ = (uniformCell D (D.G.cellOf w)).E (fun P => if f (P j) = y then 1 else 0) := by
        unfold FinLaw.E FinLaw.pr
        apply Finset.sum_congr rfl
        intro P hP
        by_cases hy : f (P j) = y
        · simp [selectedLabel, f] at hy ⊢
          simp [hy]
        · simp [selectedLabel, f] at hy ⊢
          simp [hy]
      _ = (uniformBin D (D.G.cellPatch (D.G.cellOf w))).E
          (fun B => if f B = y then 1 else 0) := hc
      _ = _ := by
        unfold FinLaw.E FinLaw.pr
        apply Finset.sum_congr rfl
        intro B hB
        by_cases hy : f B = y <;> simp [hy]
  have hi := congrArg (fun Q : FinLaw (Fin (T.S.N k)) => Q.w y)
    (uniformBin_index_marginal D (D.G.cellOf_patch w) l)
  rw [map_weight_eq_pr] at hi
  exact hpr.trans hi

/-- Averaging two independent event draws may be performed in either order. -/
theorem expect_pr_swap {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : α → β → Prop) :
    P.E (fun x => Q.pr (A x)) = Q.E (fun y => P.pr (fun x => A x y)) := by
  unfold FinLaw.E FinLaw.pr
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> ring

/-- Every unforced witness is small after integrating its actual own tape. -/
theorem unforced_witness_average (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k) (heven : IsEvenRole v)
    (a : CompatibilityWitness D v) (P : ∀ C, FinLaw (CellPool D.G C))
    {wS wL err W : ℝ} (hDisc : TwoBudgetDisc T k wS wL err)
    (he : 0 ≤ err) (heSmall : err ≤ 1 / 4)
    (hs : 2 * (a.1.1.card : ℝ) * err ≤ 1 / 10)
    (hCap : ∀ σ, ∀ hσ : D.CleanInitialPrior v σ,
      (cleanPriorLaw D v σ hσ).CapLE (Real.exp wS * (1 / 2 - err) ^ a.1.1.card))
    (hW : ∀ w : a.1.1, (binIndexLaw D.tiling_valid (D.G.patchOf w.1) (a.2.2 w)).WidthLE W)
    (hUnforced : ∀ w : a.1.1,
      FinLaw.map (P (D.G.cellOf w.1)) (selectedLabel D w.1 (a.2.1 w) (a.2.2 w)) =
        ListGateContext.lawAsFinLaw (binIndexLaw D.tiling_valid (D.G.patchOf w.1) (a.2.2 w))) :
    (FinLaw.pi P).E (witnessAverage D v a) ≤
      (a.1.1.card : ℝ) * (2 * Real.exp (W - wL)) := by
  let ρ := (a.1.1.card : ℝ) * (2 * Real.exp (W - wL))
  let ν : a.1.1 → Law (T.S.N k) := fun w =>
    binIndexLaw D.tiling_valid (D.G.patchOf w.1) (a.2.2 w)
  rw [witnessAverage_pi D K hQuant v heven a P]
  simp_rw [hUnforced]
  apply (expect_le _ _ (fun _ => ρ) ?_).trans (by simp [FinLaw.E, ← Finset.sum_mul, FinLaw.sum_one, ρ])
  intro own
  by_cases ht : D.F.typical (D.G.cellOf v) own
  · simp only [ht, ite_true]
    unfold selectedBadProbability
    rw [expect_pr_swap]
    change (D.F.fresh (D.G.cellOf v) own).E _ ≤ ρ
    calc
      _ ≤ ∑ s, (D.F.fresh (D.G.cellOf v) own).w s * ρ := by
        apply Finset.sum_le_sum
        intro s hs'
        by_cases hz : (D.F.fresh (D.G.cellOf v) own).w s = 0
        · simp [hz]
        · have hp : 0 < (D.F.fresh (D.G.cellOf v) own).w s :=
            lt_of_le_of_ne ((D.F.fresh _ _).nonneg s) (Ne.symm hz)
          have hv := D.fresh_spec.fresh_valid _ _ s ht hp
          have hc := hQuant.prior_shape v own s heven ht hv
          apply mul_le_mul_of_nonneg_left _ ((D.F.fresh _ _).nonneg s)
          simpa only [Fintype.card_coe, cleanPriorLaw, ν, ρ] using independent_pin_mass_tail_fintype hDisc PT.tiling.c
            (cleanPriorLaw D v _ hc) ν (cleanPriorLaw_supported D v _ hc) he heSmall
            (by simpa using hs) (by simpa using hCap _ hc)
            (fun w => binIndexLaw_supported D.tiling_valid _ _) hW
      _ = ρ := by rw [← Finset.sum_mul, FinLaw.sum_one, one_mul]
  · simp only [ht, ite_false]
    dsimp [ρ]
    positivity


/-- A weighted family of small subsets has a polynomial total weight. -/
theorem weighted_small_sets {α : Type*} [Fintype α] (A : Finset α)
    (B q n : ℕ) (ha : A.card ≤ n) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    (∑ p ∈ A.powerset.filter (fun p => p.card ≤ B), q ^ p.card) ≤
      (B + 1) * (n * q) ^ B := by
  let S := A.powerset.filter (fun p => p.card ≤ B)
  have hmap : ∀ p ∈ S, p.card ∈ Finset.range (B + 1) := by
    intro p hp
    have hc := (Finset.mem_filter.mp hp).2
    simpa only [Finset.mem_range] using Nat.lt_succ_of_le hc
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p : Finset α => q ^ p.card)]
  calc
    _ ≤ ∑ _s ∈ Finset.range (B + 1), (n * q) ^ B := by
      apply Finset.sum_le_sum
      intro s hs
      have hsB : s ≤ B := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
      have hf : S.filter (fun p => p.card = s) = A.powersetCard s := by
        ext p
        simp only [S, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
        constructor
        · rintro ⟨⟨hp, _⟩, hc⟩
          exact ⟨hp, hc⟩
        · rintro ⟨hp, hc⟩
          exact ⟨⟨hp, by omega⟩, hc⟩
      rw [hf]
      calc
        (∑ p ∈ A.powersetCard s, q ^ p.card) = (A.powersetCard s).card * q ^ s := by
          rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_powersetCard.mp hp).2])]
          simp
        _ = A.card.choose s * q ^ s := by rw [Finset.card_powersetCard]
        _ ≤ n ^ s * q ^ s := Nat.mul_le_mul_right _
          ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left ha s))
        _ = (n * q) ^ s := (mul_pow _ _ _).symm
        _ ≤ (n * q) ^ B := Nat.pow_le_pow_right (by nlinarith) hsB
    _ = (B + 1) * (n * q) ^ B := by simp


/-- The concrete witness family has the polynomial size stated in the paper. -/
theorem compatibility_witness_count (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (v : Pos T k) (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) (hn : 1 ≤ T.S.n k) :
    Fintype.card (CompatibilityWitness D v) ≤
      (ListGateContext.pinBudget κ + 1) *
        (T.S.n k * ((T.S.n k) ^ (κ.Ac + 1) * T.S.n k)) ^ ListGateContext.pinBudget κ := by
  let n := T.S.n k
  let L := n ^ (κ.Ac + 1)
  let B := ListGateContext.pinBudget κ
  let S := (D.externalEarly v).powerset.filter (fun p => p.card ≤ B)
  have hslots (C : D.G.Cell) : D.G.nslot C ≤ L := by
    have hh := hQuant.geometry.slots_upper C
    rw [show (κ.Ac : ℝ) + 1 = ((κ.Ac + 1 : ℕ) : ℝ) by push_cast; rfl] at hh
    simp only [Real.rpow_eq_pow] at hh
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ p : {p : Finset (Pos T k) // p ⊆ D.externalEarly v ∧ p.card ≤ B},
        (L * n) ^ p.1.card := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
      simp only [Fintype.card_fin]
      have hs : (∏ w : p.1, D.G.nslot (D.G.cellOf w.1)) ≤ L ^ p.1.card := by
        simpa using Finset.prod_le_prod' (s := Finset.univ) (fun (w : p.1) _ => hslots (D.G.cellOf w.1))
      have hd : (∏ w : p.1, (PT.tiling.P (D.G.patchOf w.1)).d) ≤ n ^ p.1.card := by
        simpa using Finset.prod_le_prod' (s := Finset.univ)
          (fun (w : p.1) _ => low_bin_size_le D hκ hlog hn (D.G.patchOf w.1))
      exact (Nat.mul_le_mul hs hd).trans_eq (mul_pow L n p.1.card).symm
    _ = ∑ p ∈ S, (L * n) ^ p.card := by
      symm
      apply Finset.sum_subtype S
      intro p
      simp [S, B]
    _ ≤ (B + 1) * (n * (L * n)) ^ B :=
      weighted_small_sets (D.externalEarly v) B (L * n) n
        (Lane_q_s17_pool.externalEarly_card_le D v) hn (by
          change 0 < L * n
          exact Nat.mul_pos (Nat.pow_pos (by dsimp [n]; omega)) (by dsimp [n]; omega))


/-- Markov at the exact compatibility threshold uses the actual own-tape average. -/
theorem witness_failure_markov (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (a : CompatibilityWitness D v) (μ : FinLaw D.PoolAssignment) (hn : 0 < T.S.n k) :
    μ.pr (witnessFailure D K hQuant v a) ≤ μ.E (witnessAverage D v a) /
      Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  have hf (pools : D.PoolAssignment) : 0 ≤ witnessAverage D v a pools := by
    unfold witnessAverage
    split_ifs
    · unfold FinLaw.pr
      apply Finset.sum_nonneg
      intro s hs
      split_ifs <;> first | exact (D.F.fresh _ _).nonneg s | exact le_rfl
    · exact le_rfl
  have ht : 0 < Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hcover (pools : D.PoolAssignment) (hb : witnessFailure D K hQuant v a pools) :
      Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) ≤ witnessAverage D v a pools := by
    have ho := hb.1 (D.G.cellOf v) (by simp [ListGateContext.scopeCells])
    simpa only [witnessAverage, ho, ite_true] using hb.2.2.le
  exact (Lane_q_s17_pool.pr_mono μ hcover).trans
    (Lane_q_s17_pool.pr_markov μ (witnessAverage D v a) _ hf ht)

/-- Concrete witness tails and the polynomial iid comparison assemble the endpoint. -/
theorem compatibility_from_witness_tails (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (hn : 2 ≤ T.S.n k) (μ : FinLaw D.PoolAssignment)
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ)
    (ε target : ℝ) (hε : 0 ≤ ε)
    (hTails : ∀ ν : FinLaw D.PoolAssignment,
      (ν = iidPoolLaw D.G hQuant.pool_support_nonempty ∨
        ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
          (iidPoolLaw D.G hQuant.pool_support_nonempty).w pools),
          ν = FinLaw.cond (iidPoolLaw D.G hQuant.pool_support_nonempty) (D.poolPinSet pin) hpin) →
      ∀ a : CompatibilityWitness D v, ν.pr (witnessFailure D K hQuant v a) ≤ ε)
    (hNumeric : (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) *
      (Fintype.card (CompatibilityWitness D v) : ℝ) * ε ≤ target) :
    μ.pr (D.compatibilityFailure v) ≤ target := by
  let f : D.PoolAssignment → ℝ := fun pools => if D.compatibilityFailure v pools then 1 else 0
  obtain ⟨ν, hν, hc⟩ := local_pool_iid_comparison D K hQuant v hn μ hμ
  have hnonneg (pools : D.PoolAssignment) : 0 ≤ f pools := by
    dsimp [f]; split_ifs <;> norm_num
  have hlocal : ∀ p q, (∀ C ∈ D.scopeCells v, p C = q C) → f p = f q := by
    intro p q hpq
    obtain ⟨ht, ha⟩ := pool_predicates_local D v p q hpq
    dsimp [f, ListGateContext.compatibilityFailure]
    simp only [ht, ha]
    split_ifs with hh <;> simp [hh]
  have hcompare := hc f hnonneg hlocal
  have he (P : FinLaw D.PoolAssignment) : P.E f = P.pr (D.compatibilityFailure v) := by
    simp [FinLaw.E, FinLaw.pr, f, mul_ite]
  rw [he μ, he ν] at hcompare
  have htail : ν.pr (D.compatibilityFailure v) ≤
      (Fintype.card (CompatibilityWitness D v) : ℝ) * ε := by
    calc
      _ ≤ ∑ a : CompatibilityWitness D v, ν.pr (witnessFailure D K hQuant v a) :=
        compatibility_witness_union D K hQuant v ν
      _ ≤ ∑ _a : CompatibilityWitness D v, ε :=
        Finset.sum_le_sum (fun a _ => hTails ν hν a)
      _ = _ := by simp
  have hfactor : 0 ≤ 1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact hcompare.trans ((mul_le_mul_of_nonneg_left htail hfactor).trans
    (by simpa only [mul_assoc] using hNumeric))


/-- A polynomial prefactor times a linear exponential beats the resampling-round tail. -/
theorem polynomial_exponential_round_tail (C c d R : ℝ)
    (hC : 0 < C) (hc : 0 < c) (hd : 0 ≤ d) (hR : 0 ≤ R) :
    ∀ᶠ n : ℝ in atTop,
      C * Real.rpow n d * Real.exp (-c * n) ≤
        Real.rpow n (-(R * (⌈(Real.log n) ^ 2⌉₊ : ℝ))) := by
  let A := 2 * R + d + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 3)).bound
    (div_pos hc (mul_pos (by norm_num : (0 : ℝ) < 2) hA))
  have hconstant := (tendsto_id : Tendsto (fun n : ℝ => n) atTop atTop).eventually_ge_atTop
    (2 * Real.log C / c)
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [hsmall, hconstant, hlog, eventually_gt_atTop (0 : ℝ)] with n hn hconst hy hpos
  let y := Real.log n
  let m := ⌈y ^ 2⌉₊
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hpow : y ^ 3 ≤ c / (2 * A) * n := by
    change ‖y ^ 3‖ ≤ c / (2 * A) * ‖n‖ at hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy0 3), abs_of_pos hpos,
      id_eq] using hn
  have hconst' : Real.log C ≤ c * n / 2 := by
    change 2 * Real.log C / c ≤ n at hconst
    have hh := (div_le_iff₀ hc).mp hconst
    nlinarith
  have hm : (m : ℝ) ≤ y ^ 2 + 1 := (Nat.ceil_lt_add_one (sq_nonneg y)).le
  have hcube : y ≤ y ^ 3 := by
    have hh : 1 ≤ y := hy
    nlinarith [sq_nonneg (y - 1), mul_nonneg (by linarith : 0 ≤ y - 1) (sq_nonneg y)]
  have hcost : d * y + R * (m : ℝ) * y ≤ (2 * R + d) * y ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hm (mul_nonneg hR hy0)
    have hd' := mul_le_mul_of_nonneg_left hcube hd
    have hR' := mul_le_mul_of_nonneg_left hcube hR
    nlinarith
  have hlinear : (2 * R + d) * y ^ 3 ≤ c * n / 2 := by
    have hp := (le_div_iff₀ (mul_pos (by norm_num) hA)).mp
      (show y ^ 3 ≤ c * n / (2 * A) by simpa only [div_mul_eq_mul_div] using hpow)
    have hm := mul_le_mul_of_nonneg_right (show 2 * R + d ≤ A by dsimp [A]; linarith)
      (pow_nonneg hy0 3)
    nlinarith
  have he : Real.log C + d * Real.log n - c * n ≤ -(R * (m : ℝ)) * Real.log n := by
    dsimp [y] at hcost
    nlinarith
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos hpos, Real.rpow_def_of_pos hpos,
    ← Real.exp_log hC, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [m, y] at he
  nlinarith


/-- Separate one distinguished coordinate from an independent finite product. -/
theorem pi_option_pr {I α : Type*} [Fintype I] [DecidableEq I] [DecidableEq (Option I)]
    [Fintype α]
    (P : FinLaw α) (Q : I → FinLaw α) (A : α → (I → α) → Prop) :
    (FinLaw.pi (Ω := fun _ : Option I => α) (fun z : Option I => match z with
      | none => P | some i => Q i)).pr (fun z => A (z none) (fun i => z (some i))) =
        P.E (fun x => (FinLaw.pi Q).pr (A x)) := by
  let e := Equiv.piOptionEquivProd (β := fun _ : Option I => α)
  unfold FinLaw.pr FinLaw.E
  have he := Fintype.sum_equiv e
    (fun z => if A (z none) (fun i => z (some i)) then
      (FinLaw.pi (Ω := fun _ : Option I => α) (fun z : Option I => match z with | none => P | some i => Q i)).w z else 0)
    (fun p => if A p.1 p.2 then
      (FinLaw.pi (Ω := fun _ : Option I => α) (fun z : Option I => match z with | none => P | some i => Q i)).w (e.symm p) else 0)
    (fun z => by rw [e.symm_apply_apply]; rfl)
  rw [he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  simp [FinLaw.pi, Fintype.prod_option, e, mul_ite]

/-- A product containing one fixed coordinate is an independent experiment on its complement. -/
theorem pi_fixed_hit_pr {I : Type*} [Fintype I] [DecidableEq I]
    {T : Stage} {k : ℕ} (c : Colour) (μ : Law (T.S.N k))
    (ν : I → Law (T.S.N k)) (j : I) (y : Fin (T.S.N k)) (z : ℝ) :
    (FinLaw.pi (fun i => if i = j then FinLaw.dirac y
      else ListGateContext.lawAsFinLaw (ν i))).pr (fun ys =>
        (∑ x, μ.w x * ∏ i, hit (T.S.E k) c x (ys i)) < z) =
      (FinLaw.pi (fun i : {i : I // i ≠ j} => ListGateContext.lawAsFinLaw (ν i.1))).pr
        (fun ys => (∑ x, μ.w x * hit (T.S.E k) c x y *
          ∏ i, hit (T.S.E k) c x (ys i)) < z) := by
  let e := Equiv.optionSubtypeNe j
  let A := fun ys : Option {i : I // i ≠ j} → Fin (T.S.N k) =>
    (∑ x, μ.w x * hit (T.S.E k) c x (ys none) *
      ∏ i : {i : I // i ≠ j}, hit (T.S.E k) c x (ys (some i))) < z
  have hp := pi_reindex_pr e
    (fun i => if i = j then FinLaw.dirac y else ListGateContext.lawAsFinLaw (ν i)) A
  have hleft : (fun ys : I → Fin (T.S.N k) => A (fun i => ys (e i))) =
      (fun ys => (∑ x, μ.w x * ∏ i, hit (T.S.E k) c x (ys i)) < z) := by
    funext ys
    dsimp [A, e]
    simp_rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => hit (T.S.E k) c _ (ys i)) j,
      mul_assoc]
  rw [hleft] at hp
  rw [hp]
  have hP : (fun i : Option {i : I // i ≠ j} =>
      if e i = j then FinLaw.dirac y else ListGateContext.lawAsFinLaw (ν (e i))) =
    (fun i : Option {i : I // i ≠ j} => match i with
      | none => FinLaw.dirac y
      | some i => ListGateContext.lawAsFinLaw (ν i.1)) := by
    funext i
    cases i with
    | none => simp [e]
    | some i => simp [e, i.2]
  rw [hP]
  change (FinLaw.pi (Ω := fun _ : Option {i : I // i ≠ j} => Fin (T.S.N k))
    (fun i : Option {i : I // i ≠ j} => match i with
      | none => FinLaw.dirac y
      | some i => ListGateContext.lawAsFinLaw (ν i.1))).pr (fun ys =>
    (∑ x, μ.w x * hit (T.S.E k) c x (ys none) *
      ∏ i, hit (T.S.E k) c x (ys (some i))) < z) = _
  have hopt := pi_option_pr (I := {i : I // i ≠ j}) (α := Fin (T.S.N k)) (FinLaw.dirac y)
    (fun i : {i : I // i ≠ j} => ListGateContext.lawAsFinLaw (ν i.1))
    (fun y ys => (∑ x, μ.w x * hit (T.S.E k) c x y *
      ∏ i, hit (T.S.E k) c x (ys i)) < z)
  simp [FinLaw.E, FinLaw.dirac] at hopt
  convert hopt using 1 <;> congr!
  funext motive i hn hs
  cases i <;> rfl

/-- Expose a forced member first; all other independent labels have small width. -/
theorem single_forced_hit_tail {I : Type*} [Fintype I] [DecidableEq I]
    {T : Stage} {k : ℕ} {wS wL err W : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL err) (c : Colour)
    (μ : Law (T.S.N k)) (ν : I → Law (T.S.N k)) (j : I) (y : Fin (T.S.N k))
    (hμ : μ.SupportedIn (T.X k)) (he : 0 ≤ err) (heSmall : err ≤ 1 / 4)
    (hs : 2 * (Fintype.card I : ℝ) * err ≤ 1 / 10)
    (hCap : μ.CapLE (Real.exp wS * (1 / 2 - err) ^ Fintype.card I))
    (hν : ∀ i, (ν i).SupportedIn (T.Y k)) (hW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.pi (fun i => if i = j then FinLaw.dirac y
      else ListGateContext.lawAsFinLaw (ν i))).pr (fun ys =>
        (∑ x, μ.w x * ∏ i, hit (T.S.E k) c x (ys i)) <
          (9 / 10 : ℝ) * Real.rpow 2 (-(Fintype.card I : ℝ))) ≤
      (if (∑ x, μ.w x * hit (T.S.E k) c x y) < 1 / 2 - err then 1 else 0) +
        (Fintype.card I : ℝ) * (2 * Real.exp (W - wL)) := by
  rw [pi_fixed_hit_pr]
  let J := {i : I // i ≠ j}
  let e := (Fintype.equivFin J).symm
  have hcard : Fintype.card J + 1 = Fintype.card I := by
    simpa [J] using Fintype.card_congr (Equiv.optionSubtypeNe j)
  have hprod (ys : J → Fin (T.S.N k)) (x : Fin (T.S.N k)) :
      (∏ i : Fin (Fintype.card J), hit (T.S.E k) c x (ys (e i))) =
        ∏ i : J, hit (T.S.E k) c x (ys i) :=
    Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hp := pi_reindex_pr e (fun i : J => ListGateContext.lawAsFinLaw (ν i.1))
    (fun ys => (∑ x, μ.w x * hit (T.S.E k) c x y *
      ∏ i, hit (T.S.E k) c x (ys i)) <
        (9 / 10 : ℝ) * Real.rpow 2 (-(Fintype.card I : ℝ)))
  simp only [hprod] at hp
  rw [hp]
  have ht := forced_first_hit_tail hDisc c μ y (fun i => ν (e i).1) hμ he
    (by linarith) (by simpa only [hcard] using hCap)
    (fun i => hν _) (fun i => hW _)
  apply le_trans _ (ht.trans ?_)
  · apply Lane_q_s17_pool.pr_mono
    intro ys hy
    exact hy.trans_le (by rw [hcard]; exact short_hit_mass_threshold _ err he heSmall hs)
  · have hc : (Fintype.card J : ℝ) ≤ Fintype.card I := by exact_mod_cast (by omega : Fintype.card J ≤ Fintype.card I)
    have hh := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 2 * Real.exp (W - wL))
    exact add_le_add (le_refl _) hh

/-- Every selected slot except the prescribed one retains its raw label marginal. -/
theorem cellLaws_selected_unforced (D : ListGateContext κ T k PT)
    (p : D.PoolPin) (w : Pos T k) (j : Fin (D.G.nslot (D.G.cellOf w)))
    (l : Fin (PT.tiling.P (D.G.patchOf w)).d)
    (hu : ∀ h : D.G.cellOf w = p.cell,
      cast (congrArg (fun C => Fin (D.G.nslot C)) h) j ≠ p.slot) :
    FinLaw.map (cellLaws D (some p) (D.G.cellOf w)) (selectedLabel D w j l) =
      ListGateContext.lawAsFinLaw (binIndexLaw D.tiling_valid (D.G.patchOf w) l) := by
  rcases p with ⟨C, slot, B⟩
  by_cases hc : D.G.cellOf w = C
  · subst C
    simp only [cellLaws, Function.update_self]
    let f : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w)) → Fin (T.S.N k) := fun B =>
      binIndexRead D.tiling_valid (D.G.patchOf w)
        (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch w)) B) l
    change FinLaw.map (pinnedCell D ⟨_, slot, B⟩) (fun P => f (P j)) = _
    rw [← map_comp (pinnedCell D ⟨_, slot, B⟩) (fun P => P j) f,
      pinnedCell_unforced_marginal D ⟨_, slot, B⟩ j (by simpa using hu rfl)]
    exact uniformBin_index_marginal D (D.G.cellOf_patch w) l
  · simp only [cellLaws, Function.update_of_ne hc]
    exact uniformCell_selected_marginal D w j l

/-- The label at a prescribed external slot is deterministic. -/
theorem cellLaws_selected_forced (D : ListGateContext κ T k PT)
    (w : Pos T k) (j : Fin (D.G.nslot (D.G.cellOf w)))
    (B : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w)))
    (l : Fin (PT.tiling.P (D.G.patchOf w)).d) :
    FinLaw.map (cellLaws D (some ⟨D.G.cellOf w, j, B⟩) (D.G.cellOf w))
      (selectedLabel D w j l) = FinLaw.dirac
        (binIndexRead D.tiling_valid (D.G.patchOf w)
          (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch w)) B) l) := by
  simp only [cellLaws, Function.update_self]
  let f : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w)) → Fin (T.S.N k) := fun B =>
    binIndexRead D.tiling_valid (D.G.patchOf w)
      (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch w)) B) l
  change FinLaw.map (pinnedCell D ⟨_, j, B⟩) (fun P => f (P j)) = _
  rw [← map_comp (pinnedCell D ⟨_, j, B⟩) (fun P => P j) f,
    pinnedCell_forced_marginal]
  apply finLaw_ext
  intro y
  simp only [FinLaw.map, FinLaw.dirac]
  rw [Finset.sum_eq_single B] <;> simp_all [f, eq_comm]


/-- Permission controls the first degree of a forced external witness; the remaining labels are iid. -/
theorem forced_witness_average (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K)
    (v : Pos T k) (heven : IsEvenRole v) (a : CompatibilityWitness D v)
    (j : a.1.1) (B : Bin PT.tiling (D.G.cellPatch (D.G.cellOf j.1)))
    (hB : hQuant.sampler.permittedBin j.1
      (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch j.1)) B))
    {wS wL W : ℝ}
    (hDisc : TwoBudgetDisc T k wS wL (2 * bstar T k))
    (he : 0 ≤ 2 * bstar T k) (heSmall : 2 * bstar T k ≤ 1 / 4)
    (hs : 2 * (a.1.1.card : ℝ) * (2 * bstar T k) ≤ 1 / 10)
    (hCap : ∀ σ, ∀ hσ : D.CleanInitialPrior v σ,
      (cleanPriorLaw D v σ hσ).CapLE
        (Real.exp wS * (1 / 2 - 2 * bstar T k) ^ a.1.1.card))
    (hW : ∀ w : a.1.1, (binIndexLaw D.tiling_valid (D.G.patchOf w.1) (a.2.2 w)).WidthLE W) :
    (FinLaw.pi (cellLaws D (some ⟨D.G.cellOf j.1, a.2.1 j, B⟩))).E
      (witnessAverage D v a) ≤ K * Real.exp (-κ.cperm * T.S.n k) +
        (a.1.1.card : ℝ) * (2 * Real.exp (W - wL)) := by
  let p : D.PoolPin := ⟨D.G.cellOf j.1, a.2.1 j, B⟩
  let B' : Bin PT.tiling (D.G.patchOf j.1) :=
    cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch j.1)) B
  let y := binIndexRead D.tiling_valid (D.G.patchOf j.1) B' (a.2.2 j)
  let ν : a.1.1 → Law (T.S.N k) := fun w =>
    binIndexLaw D.tiling_valid (D.G.patchOf w.1) (a.2.2 w)
  let ρ := (a.1.1.card : ℝ) * (2 * Real.exp (W - wL))
  let F := fun own : CellPool D.G (D.G.cellOf v) =>
    if D.F.typical (D.G.cellOf v) own then
      (D.F.fresh (D.G.cellOf v) own).pr (fun s =>
        |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
          2 * bstar T k) else 0
  have hm : ∀ w : a.1.1,
      FinLaw.map (cellLaws D (some p) (D.G.cellOf w.1))
        (selectedLabel D w.1 (a.2.1 w) (a.2.2 w)) =
      if w = j then FinLaw.dirac y else ListGateContext.lawAsFinLaw (ν w) := by
    intro w
    by_cases hw : w = j
    · subst w
      simp only [ite_true]
      exact cellLaws_selected_forced D j.1 (a.2.1 j) B (a.2.2 j)
    · rw [if_neg hw]
      apply cellLaws_selected_unforced
      intro hc
      have hh : w = j := Subtype.ext
        ((hQuant.geometry.star_distinct v heven).2 _ (a.1.2.1 w.2)
          _ (a.1.2.1 j.2) hc)
      exact False.elim (hw hh)
  have hown : cellLaws D (some p) (D.G.cellOf v) = uniformCell D (D.G.cellOf v) := by
    apply Function.update_of_ne
    exact ((hQuant.geometry.star_distinct v heven).1 _ (a.1.2.1 j.2)).symm
  rw [witnessAverage_pi D K hQuant v heven a (cellLaws D (some p)), hown]
  simp_rw [hm]
  have hpoint (own : CellPool D.G (D.G.cellOf v)) :
    (if D.F.typical (D.G.cellOf v) own then
      (FinLaw.pi (fun w : a.1.1 => if w = j then FinLaw.dirac y
        else ListGateContext.lawAsFinLaw (ν w))).E
          (selectedBadProbability D v a.1.1 own) else 0) ≤ F own + ρ := by
    by_cases ht : D.F.typical (D.G.cellOf v) own
    · simp only [ht, ite_true]
      unfold selectedBadProbability
      rw [expect_pr_swap]
      have hbound : (D.F.fresh (D.G.cellOf v) own).E (fun s =>
        (FinLaw.pi (fun w : a.1.1 => if w = j then FinLaw.dirac y
          else ListGateContext.lawAsFinLaw (ν w))).pr (fun ys =>
          (∑ x, D.F.prior (D.G.cellOf v) s v x * ∏ w : a.1.1,
            hit (T.S.E k) PT.tiling.c x (ys w)) <
              (9 / 10 : ℝ) * Real.rpow 2 (-(a.1.1.card : ℝ)))) ≤
        (D.F.fresh (D.G.cellOf v) own).pr (fun s =>
          |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
            2 * bstar T k) + ρ := by
        let H := fun s : D.F.State (D.G.cellOf v) =>
          if |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
            2 * bstar T k then (1 : ℝ) else 0
        have hsum : (D.F.fresh (D.G.cellOf v) own).E (fun s => H s + ρ) =
            (D.F.fresh (D.G.cellOf v) own).pr (fun s =>
              |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
                2 * bstar T k) + ρ := by
          simp [FinLaw.E, FinLaw.pr, H, mul_add, mul_ite, Finset.sum_add_distrib,
            ← Finset.sum_mul, FinLaw.sum_one]
        rw [← hsum]
        unfold FinLaw.E
        apply Finset.sum_le_sum
        intro s hs'
        by_cases hz : (D.F.fresh (D.G.cellOf v) own).w s = 0
        · simp [hz]
        · have hp : 0 < (D.F.fresh (D.G.cellOf v) own).w s :=
            lt_of_le_of_ne ((D.F.fresh _ _).nonneg s) (Ne.symm hz)
          have hv := D.fresh_spec.fresh_valid _ _ s ht hp
          have hc := hQuant.prior_shape v own s heven ht hv
          have hh := single_forced_hit_tail hDisc PT.tiling.c (cleanPriorLaw D v _ hc)
            ν j y (cleanPriorLaw_supported D v _ hc) he heSmall
            (by simpa using hs) (by simpa using hCap _ hc)
            (fun w => binIndexLaw_supported D.tiling_valid _ _) hW
          have hfirst :
            (if (∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) <
              1 / 2 - 2 * bstar T k then (1 : ℝ) else 0) ≤
            (if |(∑ x, D.F.prior (D.G.cellOf v) s v x * hit (T.S.E k) PT.tiling.c x y) - 1 / 2| >
              2 * bstar T k then 1 else 0) := by
            split_ifs with h1 h2 h2 <;> try norm_num
            have ha := neg_le_abs ((∑ x, D.F.prior (D.G.cellOf v) s v x *
              hit (T.S.E k) PT.tiling.c x y) - 1 / 2)
            exact False.elim (h2 (by linarith))
          have hh' := hh.trans (by
            convert add_le_add hfirst (le_refl ρ) using 1 <;> congr!
            exact Fintype.card_coe _)
          have ht' := mul_le_mul_of_nonneg_left hh' ((D.F.fresh (D.G.cellOf v) own).nonneg s)
          simpa only [cleanPriorLaw, Fintype.card_coe, H] using ht'
      simpa only [F, ht, ite_true] using hbound
    · simp only [ht, ite_false, F]
      dsimp [ρ]
      positivity
  have hh := expect_le (uniformCell D (D.G.cellOf v)) _ (fun own => F own + ρ) hpoint
  have hadd : (uniformCell D (D.G.cellOf v)).E (fun own => F own + ρ) =
      (uniformCell D (D.G.cellOf v)).E F + ρ := by
    simp only [FinLaw.E, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      FinLaw.sum_one, one_mul]
  rw [hadd] at hh
  have hperm := forced_permission_average_cell D K hK hQuant v heven j.1
    (a.1.2.1 j.2) B' hB y (binIndexRead_mem D.tiling_valid _ B' (a.2.2 j))
  exact hh.trans (by simpa only [F, ρ] using add_le_add hperm (le_refl ρ))

/-- A forbidden pinned bin cannot witness compatibility failure. -/
theorem forced_witness_forbidden (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (a : CompatibilityWitness D v) (j : a.1.1)
    (B : Bin PT.tiling (D.G.cellPatch (D.G.cellOf j.1)))
    (hB : ¬ hQuant.sampler.permittedBin j.1
      (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch j.1)) B))
    (hpin : 0 < ∑ pools ∈ D.poolPinSet ⟨D.G.cellOf j.1, a.2.1 j, B⟩,
      (iidPoolLaw D.G hQuant.pool_support_nonempty).w pools) :
    (FinLaw.cond (iidPoolLaw D.G hQuant.pool_support_nonempty)
      (D.poolPinSet ⟨D.G.cellOf j.1, a.2.1 j, B⟩) hpin).pr
        (witnessFailure D K hQuant v a) = 0 := by
  unfold FinLaw.pr
  apply Finset.sum_eq_zero
  intro pools hp
  by_cases hq : pools (D.G.cellOf j.1) (a.2.1 j) = B
  · have hn : ¬ witnessFailure D K hQuant v a pools := by
      intro hb
      apply hB
      simpa only [witnessBin, hq] using hb.2.1 j
    simp [hn]
  · simp [FinLaw.cond, ListGateContext.poolPinSet, hq]


/-- All raw and one-pin iid witnesses have the same exponential Markov bound. -/
theorem fixed_iid_witness_tail (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 ≤ K) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (hlog : 1 ≤ Real.log (T.S.n k : ℝ)) (hn : 2 ≤ T.S.n k)
    (hDisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs)
      (κ.α * T.S.n k) (2 * bstar T k))
    (heSmall : 2 * bstar T k ≤ 1 / 4)
    (hErr : 2 * (ListGateContext.pinBudget κ : ℝ) * (2 * bstar T k) ≤ 1 / 10)
    (hRoom : Real.log 2 + (ListGateContext.pinBudget κ : ℝ) * Real.log 4 +
      (K + 1) * Real.log (T.S.n k : ℝ) ≤ Real.rpow (T.S.n k : ℝ) κ.xs)
    (v : Pos T k) (heven : IsEvenRole v) (ν : FinLaw D.PoolAssignment)
    (hν : ν = iidPoolLaw D.G hQuant.pool_support_nonempty ∨
      ∃ (p : D.PoolPin) (hp : 0 < ∑ pools ∈ D.poolPinSet p,
        (iidPoolLaw D.G hQuant.pool_support_nonempty).w pools),
        ν = FinLaw.cond (iidPoolLaw D.G hQuant.pool_support_nonempty) (D.poolPinSet p) hp)
    (a : CompatibilityWitness D v) :
    ν.pr (witnessFailure D K hQuant v a) ≤
      (K * Real.exp (-κ.cperm * T.S.n k) +
        (ListGateContext.pinBudget κ : ℝ) *
          (2 * Real.exp ((K + 1) * Real.log (T.S.n k : ℝ) - κ.α * T.S.n k))) /
        Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  let ε := K * Real.exp (-κ.cperm * T.S.n k) +
    (ListGateContext.pinBudget κ : ℝ) *
      (2 * Real.exp ((K + 1) * Real.log (T.S.n k : ℝ) - κ.α * T.S.n k))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have he : 0 ≤ 2 * bstar T k := by unfold bstar; positivity
  have hcard : (a.1.1.card : ℝ) ≤ ListGateContext.pinBudget κ := by exact_mod_cast a.1.2.2
  have hs : 2 * (a.1.1.card : ℝ) * (2 * bstar T k) ≤ 1 / 10 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) he).trans hErr
  have hCap := fun σ (hσ : D.CleanInitialPrior v σ) =>
    clean_prior_short_cap D K hK hQuant hκ hlog (2 * bstar T k) he heSmall hRoom
      v σ hσ a.1.1.card a.1.2.2
  have hW := fun w : a.1.1 => low_bin_index_width D K hK hQuant hκ hlog
    (by omega) (D.G.patchOf w.1) (a.2.2 w)
  have hmean (P : ∀ C, FinLaw (CellPool D.G C))
      (hU : ∀ w : a.1.1,
        FinLaw.map (P (D.G.cellOf w.1)) (selectedLabel D w.1 (a.2.1 w) (a.2.2 w)) =
          ListGateContext.lawAsFinLaw (binIndexLaw D.tiling_valid (D.G.patchOf w.1) (a.2.2 w))) :
      (FinLaw.pi P).E (witnessAverage D v a) ≤ ε := by
    have hh := unforced_witness_average D K hQuant v heven a P hDisc he heSmall hs hCap hW hU
    have hc := mul_le_mul_of_nonneg_right hcard
      (by positivity : 0 ≤ 2 * Real.exp ((K + 1) * Real.log (T.S.n k : ℝ) - κ.α * T.S.n k))
    dsimp [ε]
    exact hh.trans (by linarith [mul_nonneg hK (Real.exp_pos (-κ.cperm * T.S.n k)).le])
  have hfinish (Q : FinLaw D.PoolAssignment) (hQ : Q.E (witnessAverage D v a) ≤ ε) :
      Q.pr (witnessFailure D K hQuant v a) ≤
        ε / Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) :=
    (witness_failure_markov D K hQuant v a Q (by omega)).trans
      (div_le_div_of_nonneg_right hQ (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rcases hν with rfl | ⟨p, hp, rfl⟩
  · apply hfinish
    rw [iidPoolLaw_eq_pi]
    exact hmean (uniformCell D) (fun w => uniformCell_selected_marginal D _ _ _)
  · rcases p with ⟨C, slot, B⟩
    by_cases hc : ∃ j : a.1.1, D.G.cellOf j.1 = C
    · obtain ⟨j, hc⟩ := hc
      subst C
      by_cases hslot : slot = a.2.1 j
      · subst slot
        by_cases hB : hQuant.sampler.permittedBin j.1
          (cast (congrArg (Bin PT.tiling) (D.G.cellOf_patch j.1)) B)
        · apply hfinish
          rw [pinned_iidPoolLaw_eq_pi]
          have hh := forced_witness_average D K hK hQuant v heven a j B hB hDisc
            he heSmall hs hCap hW
          have hh' := mul_le_mul_of_nonneg_right hcard
            (by positivity : 0 ≤ 2 * Real.exp ((K + 1) * Real.log (T.S.n k : ℝ) - κ.α * T.S.n k))
          exact hh.trans (by dsimp [ε]; linarith)
        · rw [forced_witness_forbidden D K hQuant v a j B hB]
          exact div_nonneg hε (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · apply hfinish
        rw [pinned_iidPoolLaw_eq_pi]
        apply hmean
        intro w
        apply cellLaws_selected_unforced
        intro hw
        have hwj : w = j := Subtype.ext
          ((hQuant.geometry.star_distinct v heven).2 _ (a.1.2.1 w.2)
            _ (a.1.2.1 j.2) hw)
        subst w
        simpa using (Ne.symm hslot)
    · apply hfinish
      rw [pinned_iidPoolLaw_eq_pi]
      apply hmean
      intro w
      apply cellLaws_selected_unforced
      intro hw
      exact False.elim (hc ⟨w, hw⟩)

/-- A constant and a logarithmic term fit inside any positive power budget. -/
theorem eventually_logarithmic_room (r c C a : ℝ) (hr : 0 < r) (hc : 0 < c) (ha : 0 ≤ a) :
    ∀ᶠ n : ℝ in atTop, C + a * Real.log n ≤ c * Real.rpow n r := by
  simp only [Real.rpow_eq_pow]
  have hlog := (isLittleO_log_rpow_atTop hr).bound (div_pos hc (by positivity : 0 < 2 * (a + 1)))
  have hpow := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * |C| / c)
  filter_upwards [hlog, hpow, eventually_ge_atTop (0 : ℝ)] with n hn hp hnonneg
  have hn' : |Real.log n| ≤ c / (2 * (a + 1)) * n ^ r := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnonneg r), Real.rpow_eq_pow] using hn
  have hcC : 2 * C ≤ c * n ^ r := by
    have hh := (div_le_iff₀ hc).mp hp
    nlinarith [le_abs_self C]
  have hl : a * Real.log n ≤ (c / 2) * n ^ r := by
    have hbound := mul_le_mul_of_nonneg_left hn' ha
    have hfac : a * (c / (2 * (a + 1))) ≤ c / 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < 2 * (a + 1))).mpr
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hfac (Real.rpow_nonneg hnonneg r)
    nlinarith [le_abs_self (Real.log n)]
  linarith

/-- All analytic budgets and the polynomial witness union fit before one common index. -/
theorem eventually_compatibility_budgets (κ : CConsts) (hκ : κ.Admissible)
    (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℝ in atTop,
      2 ≤ n ∧ 1 ≤ Real.log n ∧
      2 * Real.rpow n (-1 + (0.04 : ℝ)) ≤ 1 / 4 ∧
      2 * (ListGateContext.pinBudget κ : ℝ) * (2 * Real.rpow n (-1 + (0.04 : ℝ))) ≤ 1 / 10 ∧
      Real.log 2 + (ListGateContext.pinBudget κ : ℝ) * Real.log 4 +
        (K + 1) * Real.log n ≤ Real.rpow n κ.xs ∧
      (1 + Real.rpow n (-3 : ℝ)) *
        ((ListGateContext.pinBudget κ : ℝ) + 1) *
        Real.rpow n (((κ.Ac : ℝ) + 3) * ListGateContext.pinBudget κ) *
        ((K * Real.exp (-κ.cperm * n) + (ListGateContext.pinBudget κ : ℝ) *
          (2 * Real.exp ((K + 1) * Real.log n - κ.α * n))) /
          Real.rpow n (-(2 * (κ.R : ℝ)))) ≤
        Real.rpow n (-((κ.R : ℝ) * (⌈(Real.log n) ^ 2⌉₊ : ℝ))) := by
  simp only [Real.rpow_eq_pow]
  let B := (ListGateContext.pinBudget κ : ℝ)
  let C := 2 * (B + 1) * (K + 2 * B)
  let d := ((κ.Ac : ℝ) + 3) * B + 2 * (κ.R : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hgap : 0 < κ.α - κ.cperm := by linarith [hκ.cperm_rng.2, hκ.α_rng.1]
  have hroom := eventually_logarithmic_room κ.xs 1
    (Real.log 2 + B * Real.log 4) (K + 1) hκ.xs_rng.1 (by norm_num) (by linarith)
  have hwidth := eventually_logarithmic_room 1 (κ.α - κ.cperm) 0 (K + 1)
    (by norm_num) hgap (by linarith)
  have he : Tendsto (fun n : ℝ => 2 * n ^ (-1 + (0.04 : ℝ))) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 - 0.04)).const_mul 2 using 1 <;> norm_num
  have hbe : Tendsto (fun n : ℝ => (4 * B) * n ^ (-1 + (0.04 : ℝ))) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 - 0.04)).const_mul (4 * B) using 1 <;> norm_num
  have htail := polynomial_exponential_round_tail C κ.cperm d (κ.R : ℝ)
    hC hκ.cperm_rng.1 hd (Nat.cast_nonneg _)
  simp only [Real.rpow_eq_pow] at hroom hwidth htail
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hbe.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10)),
    hroom, hwidth, htail] with n hn hlog he hbe hroom hwidth htail
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  refine ⟨hn, hlog, ?_, ?_, ?_, ?_⟩
  · convert he.le using 1 <;> norm_num
  · convert hbe.le using 1 <;> norm_num <;> ring
  · simpa only [one_mul, B] using hroom
  · have hpow : n ^ (-3 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    have hexp : Real.exp ((K + 1) * Real.log n - κ.α * n) ≤ Real.exp (-κ.cperm * n) := by
      apply Real.exp_le_exp.mpr
      simp only [zero_add, Real.rpow_one] at hwidth
      nlinarith
    have hnum : K * Real.exp (-κ.cperm * n) + B *
        (2 * Real.exp ((K + 1) * Real.log n - κ.α * n)) ≤
        (K + 2 * B) * Real.exp (-κ.cperm * n) := by
      have hh := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * B)
      nlinarith
    have hdiv : 1 / n ^ (-(2 * (κ.R : ℝ))) = n ^ (2 * (κ.R : ℝ)) := by
      rw [Real.rpow_neg hn0.le]
      simp
    have heq : 2 * (B + 1) * n ^ (((κ.Ac : ℝ) + 3) * B) *
        (((K + 2 * B) * Real.exp (-κ.cperm * n)) /
          n ^ (-(2 * (κ.R : ℝ)))) = C * n ^ d * Real.exp (-κ.cperm * n) := by
      rw [div_eq_mul_one_div, hdiv]
      dsimp [C, d]
      rw [Real.rpow_add hn0]
      ring
    apply le_trans _ htail
    change (1 + n ^ (-3 : ℝ)) * (B + 1) * n ^ (((κ.Ac : ℝ) + 3) * B) *
      ((K * Real.exp (-κ.cperm * n) + B * (2 * Real.exp ((K + 1) * Real.log n - κ.α * n))) /
        n ^ (-(2 * (κ.R : ℝ)))) ≤ _
    rw [← heq]
    have hfac : 0 ≤ (1 + n ^ (-3 : ℝ)) * (B + 1) *
        n ^ (((κ.Ac : ℝ) + 3) * B) := by positivity
    calc
      _ ≤ (1 + n ^ (-3 : ℝ)) * (B + 1) * n ^ (((κ.Ac : ℝ) + 3) * B) *
          (((K + 2 * B) * Real.exp (-κ.cperm * n)) /
            n ^ (-(2 * (κ.R : ℝ)))) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum (by positivity)) hfac
      _ ≤ _ := by
        gcongr
        linarith


/-- The concrete witness cover, pin estimates and numerical budget imply compatibility. -/
theorem fixed_pool_compatibility (D : ListGateContext κ T k PT)
    (K : ℝ) (hK : 0 < K) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (hn : 2 ≤ T.S.n k) (hlog : 1 ≤ Real.log (T.S.n k : ℝ))
    (hDisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs)
      (κ.α * T.S.n k) (2 * bstar T k))
    (heSmall : 2 * bstar T k ≤ 1 / 4)
    (hErr : 2 * (ListGateContext.pinBudget κ : ℝ) * (2 * bstar T k) ≤ 1 / 10)
    (hRoom : Real.log 2 + (ListGateContext.pinBudget κ : ℝ) * Real.log 4 +
      (K + 1) * Real.log (T.S.n k : ℝ) ≤ Real.rpow (T.S.n k : ℝ) κ.xs)
    (hNumeric : (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) *
      ((ListGateContext.pinBudget κ : ℝ) + 1) *
      Real.rpow (T.S.n k : ℝ) (((κ.Ac : ℝ) + 3) * ListGateContext.pinBudget κ) *
      ((K * Real.exp (-κ.cperm * T.S.n k) + (ListGateContext.pinBudget κ : ℝ) *
        (2 * Real.exp ((K + 1) * Real.log (T.S.n k : ℝ) - κ.α * T.S.n k))) /
        Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))) ≤
      Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * initialResamplingRounds T k)))
    (v : Pos T k) (heven : IsEvenRole v) (μ : FinLaw D.PoolAssignment)
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ) :
    μ.pr (D.compatibilityFailure v) ≤ Real.rpow (T.S.n k : ℝ)
      (-((κ.R : ℝ) * initialResamplingRounds T k)) := by
  let B := ListGateContext.pinBudget κ
  let ε := (K * Real.exp (-κ.cperm * T.S.n k) + (B : ℝ) *
    (2 * Real.exp ((K + 1) * Real.log (T.S.n k : ℝ) - κ.α * T.S.n k))) /
      Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hcount : (Fintype.card (CompatibilityWitness D v) : ℝ) ≤
      ((B : ℝ) + 1) * Real.rpow (T.S.n k : ℝ) (((κ.Ac : ℝ) + 3) * B) := by
    have hh := compatibility_witness_count D K hQuant hκ v hlog (by omega)
    have hp : T.S.n k * ((T.S.n k) ^ (κ.Ac + 1) * T.S.n k) = (T.S.n k) ^ (κ.Ac + 3) := by
      simp only [pow_add, pow_one]
      ring
    rw [hp] at hh
    simp only [Real.rpow_eq_pow]
    rw [show ((κ.Ac : ℝ) + 3) * B = (((κ.Ac + 3) * B : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
    exact_mod_cast hh
  apply compatibility_from_witness_tails D K hQuant v hn μ hμ ε _ hε
  · intro ν hν a
    exact fixed_iid_witness_tail D K hK.le hQuant hκ hlog hn hDisc heSmall hErr hRoom v heven ν hν a
  · have hf : 0 ≤ 1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ) :=
      add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcount hf) hε
    exact hh.trans (by simpa only [B, ε, mul_assoc] using hNumeric)

end HypercubeRamsey.Lane_sol_s17_compat
