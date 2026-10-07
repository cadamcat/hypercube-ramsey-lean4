import HypercubeRamsey.S17.Nodes_sol_s17_pool_experiment

set_option maxHeartbeats 1000000

namespace HypercubeRamsey.Lane_sol_s17_moment

open Classical
open Filter
open scoped BigOperators
open S16.Lane_q_s16_comp2
open Lane_sol_s17_pool

private theorem probability_le_one {α : Type*} [Fintype α] (P : FinLaw α)
    (A : α → Prop) : P.pr A ≤ 1 := by
  classical
  calc
    _ ≤ ∑ a, P.w a := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs <;> simp [P.nonneg a]
    _ = 1 := P.sum_one

/-- Integrate a selected set of independent coordinates while fixing its complement. -/
theorem pi_E_split {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset I) (f : (∀ i, Ω i) → ℝ) :
    (FinLaw.pi P).E f =
      (FinLaw.pi fun i : {i // i ∉ S} => P i.1).E (fun outside =>
        (FinLaw.pi fun i : {i // i ∈ S} => P i.1).E (fun inside =>
          f (fun i => if hi : i ∈ S then inside ⟨i, hi⟩ else outside ⟨i, hi⟩))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω
  unfold FinLaw.E
  rw [Fintype.sum_equiv e _ (fun p => (FinLaw.pi P).w (e.symm p) * f (e.symm p))
    (fun s => by simp), Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outside ho
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inside hi
  change (∏ i, (P i).w (e.symm (inside, outside) i)) * f (e.symm (inside, outside)) = _
  have hprod : (∏ i, (P i).w (e.symm (inside, outside) i)) =
      (∏ i : {i // i ∈ S}, (P i.1).w (inside i)) *
        ∏ i : {i // i ∉ S}, (P i.1).w (outside i) := by
    calc
      _ = (∏ i : {i // i ∈ S}, (P i.1).w (e.symm (inside, outside) i.1)) *
          ∏ i : {i // i ∉ S}, (P i.1).w (e.symm (inside, outside) i.1) :=
        by
          let g := fun i => (P i).w (e.symm (inside, outside) i)
          have hs := Finset.prod_subtype (p := fun i => i ∈ S) (F := inferInstance)
            S (fun _ => Iff.rfl) g
          have ht := Finset.prod_subtype (p := fun i => i ∉ S) (F := inferInstance)
            Sᶜ (fun _ => Finset.mem_compl) g
          exact (Finset.prod_mul_prod_compl S g).symm.trans (congrArg₂ (· * ·) hs ht)
      _ = _ := by
        congr 1 <;> apply Finset.prod_congr rfl <;> intro i hi <;>
          simp only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, i.2, dite_true, dite_false]
  rw [hprod]
  dsimp [e, Equiv.piEquivPiSubtypeProd, FinLaw.pi]
  ring

/-- The same split for an arbitrary finite sum, without normalization assumptions. -/
theorem sum_pi_split {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (S : Finset I) (W : I → α → ℝ) (f : (I → α) → ℝ) :
    (∑ ys : I → α, (∏ i, W i (ys i)) * f ys) =
      ∑ inside : {i // i ∈ S} → α, (∏ i, W i.1 (inside i)) *
        ∑ outside : {i // i ∉ S} → α, (∏ i, W i.1 (outside i)) *
          f (fun i => if hi : i ∈ S then inside ⟨i, hi⟩ else outside ⟨i, hi⟩) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => α)
  rw [Fintype.sum_equiv e _ (fun p => (∏ i, W i (e.symm p i)) * f (e.symm p))
    (fun s => by simp), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro inside hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outside ho
  have hprod : (∏ i, W i (e.symm (inside, outside) i)) =
      (∏ i : {i // i ∈ S}, W i.1 (inside i)) *
        ∏ i : {i // i ∉ S}, W i.1 (outside i) := by
    calc
      _ = (∏ i : {i // i ∈ S}, W i.1 (e.symm (inside, outside) i.1)) *
          ∏ i : {i // i ∉ S}, W i.1 (e.symm (inside, outside) i.1) :=
        by
          let g := fun i => W i (e.symm (inside, outside) i)
          have hs := Finset.prod_subtype (p := fun i => i ∈ S) (F := inferInstance)
            S (fun _ => Iff.rfl) g
          have ht := Finset.prod_subtype (p := fun i => i ∉ S) (F := inferInstance)
            Sᶜ (fun _ => Finset.mem_compl) g
          exact (Finset.prod_mul_prod_compl S g).symm.trans (congrArg₂ (· * ·) hs ht)
      _ = _ := by
        congr 1 <;> apply Finset.prod_congr rfl <;> intro i hi <;>
          simp only [e, Equiv.piEquivPiSubtypeProd, Equiv.coe_fn_symm_mk, i.2, dite_true, dite_false]
  rw [hprod]
  dsimp [e, Equiv.piEquivPiSubtypeProd]
  ring

/-- Dirac coordinates in a pinned product experiment are substituted exactly. -/
theorem pinned_pi_E {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (P : I → FinLaw α) (S : Finset I) (fixed : I → α) (f : (I → α) → ℝ) :
    (FinLaw.pi fun i => if i ∈ S then FinLaw.dirac (fixed i) else P i).E f =
      (FinLaw.pi fun i : {i // i ∉ S} => P i.1).E (fun outside =>
        f (fun i => if hi : i ∈ S then fixed i else outside ⟨i, hi⟩)) := by
  classical
  rw [pi_E_split _ S]
  have hOutside : (fun i : {i // i ∉ S} =>
      if i.1 ∈ S then FinLaw.dirac (fixed i.1) else P i.1) = fun i => P i.1 := by
    funext i
    simp [i.2]
  have hInside : (fun i : {i // i ∈ S} =>
      if i.1 ∈ S then FinLaw.dirac (fixed i.1) else P i.1) =
      fun i => FinLaw.dirac (fixed i.1) := by
    funext i
    simp [i.2]
  rw [hOutside, hInside]
  congr 1
  funext outside
  unfold FinLaw.E
  rw [Finset.sum_eq_single (fun i => fixed i.1)]
  · simp [FinLaw.pi, FinLaw.dirac]
  · intro ys hys hne
    have hz : (FinLaw.pi fun i : {i // i ∈ S} => FinLaw.dirac (fixed i.1)).w ys = 0 := by
      change (∏ i : {i // i ∈ S}, (FinLaw.dirac (fixed i.1)).w (ys i)) = 0
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [FinLaw.dirac, hi])
    rw [hz, zero_mul]
  · simp

/-- Weighted pinned coordinates may be summed outside the independent unpinned law. -/
theorem weighted_pinned_sum {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (P : I → FinLaw α) (S : Finset I) (W : I → α → ℝ)
    (base : α) (f : (I → α) → ℝ) :
    (∑ ys : I → α, (∏ i, if i ∈ S then W i (ys i) else (P i).w (ys i)) * f ys) =
      ∑ fixed : {i // i ∈ S} → α, (∏ i, W i.1 (fixed i)) *
        (FinLaw.pi fun i => if hi : i ∈ S then FinLaw.dirac (fixed ⟨i, hi⟩)
          else P i).E f := by
  classical
  rw [sum_pi_split S (fun i y => if i ∈ S then W i y else (P i).w y) f]
  apply Finset.sum_congr rfl
  intro fixed hf
  have hprod : (∏ i : {i // i ∈ S},
      if i.1 ∈ S then W i.1 (fixed i) else (P i.1).w (fixed i)) =
      ∏ i : {i // i ∈ S}, W i.1 (fixed i) := by simp
  rw [hprod]
  congr 1
  let extend : I → α := fun i => if hi : i ∈ S then fixed ⟨i, hi⟩ else base
  have hLaw : (fun i => if hi : i ∈ S then FinLaw.dirac (fixed ⟨i, hi⟩) else P i) =
      fun i => if i ∈ S then FinLaw.dirac (extend i) else P i := by
    funext i
    by_cases hi : i ∈ S <;> simp [hi, extend]
  rw [hLaw, pinned_pi_E]
  unfold FinLaw.E
  apply Finset.sum_congr rfl
  intro outside ho
  have hp : (∏ i : {i // i ∉ S},
      if i.1 ∈ S then W i.1 (outside i) else (P i.1).w (outside i)) =
      ∏ i : {i // i ∉ S}, (P i.1).w (outside i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [i.2, ite_false]
  rw [hp]
  congr 1
  apply congrArg f
  funext i
  by_cases hi : i ∈ S <;> simp [extend, hi]

/-- A sparse pinned trial with weighted labels pays only the total pinned weight. -/
theorem weighted_pinned_bound {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (P : I → FinLaw α) (S : Finset I) (W : I → α → ℝ) (base : α)
    (f : (I → α) → ℝ) (c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hW : ∀ i y, 0 ≤ W i y) (hmass : ∀ i ∈ S, (∑ y, W i y) ≤ c)
    (htrial : ∀ fixed : {i // i ∈ S} → α,
      (FinLaw.pi fun i => if hi : i ∈ S then FinLaw.dirac (fixed ⟨i, hi⟩)
        else P i).E f ≤ δ) :
    (∑ ys : I → α, (∏ i, if i ∈ S then W i (ys i) else (P i).w (ys i)) * f ys) ≤
      c ^ S.card * δ := by
  classical
  rw [weighted_pinned_sum P S W base f]
  calc
    _ ≤ ∑ fixed : {i // i ∈ S} → α, (∏ i, W i.1 (fixed i)) * δ := by
      apply Finset.sum_le_sum
      intro fixed hf
      exact mul_le_mul_of_nonneg_left (htrial fixed)
        (Finset.prod_nonneg (fun i _ => hW i.1 (fixed i)))
    _ = (∏ i : {i // i ∈ S}, ∑ y, W i.1 y) * δ := by
      rw [← Finset.sum_mul, ← Fintype.prod_sum]
    _ ≤ c ^ S.card * δ := by
      apply mul_le_mul_of_nonneg_right _ hδ
      calc
        _ ≤ ∏ _i : {i // i ∈ S}, c := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact Finset.sum_nonneg (fun y _ => hW i.1 y)
          · intro i hi
            exact hmass i.1 i.2
        _ = c ^ S.card := by simp

/-- Compatibility specialized to one set of trial pins; it reads no external pools. -/
def ownTrialCompatible {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : D.F.Pool (D.G.cellOf v)) (pins : Finset (Pos T k))
    (fixed : Pos T k → Fin (T.S.N k)) : Prop :=
  (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
    D.pinnedStatePriorMass v s pins fixed <
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ))) ≤
    Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))

/-- A compatible own tape and independent remaining labels cost at most two tail budgets. -/
theorem own_compatible_sparse_trial {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K)
    (v : Pos T k) (heven : IsEvenRole v)
    (P : D.F.Pool (D.G.cellOf v)) (htyp : D.F.typical (D.G.cellOf v) P)
    (pins : Finset (Pos T k)) (fixed : Pos T k → Fin (T.S.N k))
    (hcompat : ownTrialCompatible D v P pins fixed)
    (hEstimate : ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤ D.pinnedPriorMass v σ pins fixed →
      (D.pinnedLabelLaw v pins fixed).pr
        (fun ys => D.gateBad v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
          Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))) :
    (FinLaw.bind (D.F.fresh (D.G.cellOf v) P) (fun _ => D.pinnedLabelLaw v pins fixed)).pr
      (fun ω => D.gateBad v (D.F.prior (D.G.cellOf v) ω.1 v)
        (D.labelsOfPinnedSample v (T.S.N_pos k) ω.2)) ≤
          2 * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  classical
  let δ : ℝ := Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))
  have hδ : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let Q := D.F.fresh (D.G.cellOf v) P
  let bad := fun s : D.F.State (D.G.cellOf v) =>
    D.pinnedStatePriorMass v s pins fixed <
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ))
  let g := fun s : D.F.State (D.G.cellOf v) =>
    (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => D.gateBad v (D.F.prior (D.G.cellOf v) s v)
        (D.labelsOfPinnedSample v (T.S.N_pos k) ys))
  have hpoint : ∀ s, Q.w s * g s ≤ Q.w s * ((if bad s then 1 else 0) + δ) := by
    intro s
    by_cases hz : Q.w s = 0
    · simp [hz]
    · have hpos : 0 < Q.w s := lt_of_le_of_ne (Q.nonneg s) (Ne.symm hz)
      have hsv := D.fresh_spec.fresh_valid (D.G.cellOf v) P s htyp hpos
      have hclean := hQuant.prior_shape v P s heven htyp hsv
      have hvalid : D.ValidInitialPrior v (D.F.prior (D.G.cellOf v) s v) :=
        ⟨hclean, ⟨P, s, htyp, hsv, fun _ => rfl⟩⟩
      apply mul_le_mul_of_nonneg_left _ (Q.nonneg s)
      by_cases hbad : bad s
      · simpa [hbad] using (probability_le_one (D.pinnedLabelLaw v pins fixed)
          (fun ys => D.gateBad v (D.F.prior (D.G.cellOf v) s v)
            (D.labelsOfPinnedSample v (T.S.N_pos k) ys))).trans
          (by linarith : (1 : ℝ) ≤ 1 + δ)
      · have hmass : (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤
            D.pinnedPriorMass v (D.F.prior (D.G.cellOf v) s v) pins fixed := by
          rw [Lane_q_s17_pool.pinnedPriorMass_eq_hits D D.tiling_valid v
            (D.F.prior (D.G.cellOf v) s v) hclean pins fixed]
          exact le_of_not_gt hbad
        simpa [hbad, g, δ] using hEstimate _ hvalid hmass
  rw [Lane_sol_s17_pool.bind_pr]
  change Q.E g ≤ 2 * δ
  calc
    _ ≤ ∑ s, Q.w s * ((if bad s then 1 else 0) + δ) :=
      Finset.sum_le_sum (fun s _ => hpoint s)
    _ = Q.pr bad + δ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Q.sum_one, one_mul]
      congr 1
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hb : bad s <;> simp [hb]
    _ ≤ δ + δ := by
      exact add_le_add (show Q.pr bad ≤ δ from hcompat) (le_refl δ)
    _ = 2 * δ := by ring

/-- Distinct slot images integrate independently, including for dependent slot types. -/
theorem pi_E_injective_prod {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (P : ∀ c, FinLaw (Ω c)) (e : I → C) (he : Function.Injective e)
    (W : ∀ i, Ω (e i) → ℝ) :
    (FinLaw.pi P).E (fun z => ∏ i, W i (z (e i))) = ∏ i, (P (e i)).E (W i) := by
  classical
  have h := pi_E_injective_readouts P e he (fun _ => id) (fun z => ∏ i, W i (z i))
  dsimp only [id] at h
  rw [h]
  rw [Lane_q_s17_pool.pi_expect_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact map_expect _ id _

/-- Independent trial-label sums factor even when their pinned weight vectors differ. -/
theorem trial_product_factorization {I J α : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype α]
    (W : I → J → α → ℝ) (f : I → (J → α) → ℝ) :
    (∑ ys : I → J → α, (∏ i, ∏ j, W i j (ys i j)) * ∏ i, f i (ys i)) =
      ∏ i, ∑ row : J → α, (∏ j, W i j (row j)) * f i row := by
  classical
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (row : J → α) => (∏ j, W i j (row j)) * f i row)).symm

/-- One weight budget per pin and one tail budget per sparse trial multiply. -/
theorem sparse_trial_product_bound {I J α : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype α]
    (P : J → FinLaw α) (pins : I → Finset J) (W : I → J → α → ℝ)
    (base : α) (f : I → (J → α) → ℝ) (c : ℝ) (δ : I → ℝ)
    (hc : 0 ≤ c) (hδ : ∀ i, 0 ≤ δ i)
    (hW : ∀ i j y, 0 ≤ W i j y) (hmass : ∀ i j, j ∈ pins i → (∑ y, W i j y) ≤ c)
    (hf : ∀ i ys, 0 ≤ f i ys)
    (htrial : ∀ i (fixed : {j // j ∈ pins i} → α),
      (FinLaw.pi fun j => if hj : j ∈ pins i then FinLaw.dirac (fixed ⟨j, hj⟩)
        else P j).E (f i) ≤ δ i) :
    (∑ ys : I → J → α,
      (∏ i, ∏ j, if j ∈ pins i then W i j (ys i j) else (P j).w (ys i j)) *
        ∏ i, f i (ys i)) ≤ c ^ (∑ i, (pins i).card) * ∏ i, δ i := by
  classical
  have hfact := trial_product_factorization
    (fun i j y => if j ∈ pins i then W i j y else (P j).w y) f
  rw [hfact]
  calc
    _ ≤ ∏ i, c ^ (pins i).card * δ i := by
      apply Finset.prod_le_prod₀
      · intro i hi
        apply Finset.sum_nonneg
        intro ys hys
        apply mul_nonneg _ (hf i ys)
        apply Finset.prod_nonneg
        intro j hj
        split_ifs
        · exact hW i j (ys j)
        · exact (P j).nonneg (ys j)
      · intro i hi
        exact weighted_pinned_bound P (pins i) (W i) base (f i) c (δ i) hc (hδ i)
          (hW i) (hmass i) (htrial i)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Flattening cell/slot coordinates preserves the complete independent pool law. -/
theorem pi_E_curry {C : Type*} [Fintype C] [DecidableEq C]
    {J : C → Type*} [∀ c, Fintype (J c)]
    {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (P : ∀ c, J c → FinLaw (Ω c)) (f : (∀ c, J c → Ω c) → ℝ) :
    (FinLaw.pi fun c => FinLaw.pi (P c)).E f =
      (FinLaw.pi fun a : Σ c, J c => P a.1 a.2).E
        (fun z => f (fun c j => z ⟨c, j⟩)) := by
  classical
  let e := Equiv.piCurry (fun c (_ : J c) => Ω c)
  unfold FinLaw.E
  rw [Fintype.sum_equiv e.symm _
    (fun z => (FinLaw.pi fun c => FinLaw.pi (P c)).w (e z) * f (e z))
    (fun s => by simp)]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  change (∏ c, ∏ j, (P c j).w (z ⟨c, j⟩)) = ∏ a : Σ c, J c, (P a.1 a.2).w (z a)
  exact (Fintype.prod_sigma (fun a : Σ c, J c => (P a.1 a.2).w (z a))).symm

/-- The actual raw iid pool experiment is the product of its uniform physical bins. -/
theorem iid_pool_flat_E {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hpools : (permPools D.G).Nonempty)
    (hB : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (f : D.PoolAssignment → ℝ) :
    (iidPoolLaw D.G hpools).E f =
      (FinLaw.pi fun a : Σ C : D.G.Cell, Fin (D.G.nslot C) =>
        FinLaw.uniform Finset.univ (hB a.1)).E (fun z => f (fun C j => z ⟨C, j⟩)) := by
  classical
  let e : (∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C),
      Bin PT.tiling (D.G.cellPatch a.1)) ≃ D.PoolAssignment :=
    Equiv.piCurry (fun C (_ : Fin (D.G.nslot C)) => Bin PT.tiling (D.G.cellPatch C))
  have hFlat : (Finset.univ : Finset (∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C),
      Bin PT.tiling (D.G.cellPatch a.1))).Nonempty :=
    ⟨e.symm hpools.choose, Finset.mem_univ _⟩
  have hUniform := uniform_pi (fun a : Σ C : D.G.Cell, Fin (D.G.nslot C) => hB a.1) hFlat
  have hW (z : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C),
      Bin PT.tiling (D.G.cellPatch a.1)) :
      (FinLaw.pi fun a : Σ C : D.G.Cell, Fin (D.G.nslot C) =>
        FinLaw.uniform Finset.univ (hB a.1)).w z =
        1 / (Fintype.card D.PoolAssignment : ℝ) := by
    have h := congrArg (fun Q => Q.w z) hUniform
    simpa only [FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ,
      Fintype.card_congr e] using h
  have hRaw (pools : D.PoolAssignment) : (iidPoolLaw D.G hpools).w pools =
      1 / (Fintype.card D.PoolAssignment : ℝ) := by
    simp only [iidPoolLaw, FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ]
  unfold FinLaw.E
  simp_rw [hRaw]
  rw [Fintype.sum_equiv e.symm _
    (fun z => (1 / (Fintype.card D.PoolAssignment : ℝ)) * f (e z)) (fun _ => by simp)]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hW]
  rfl

/-- A trial with more than the pin budget consumes at least one full budget of occurrences. -/
theorem excessive_trials_count {I J : Type*} [Fintype I] [DecidableEq I]
    (pins : I → Finset J) (s0 : ℕ) :
    (Finset.univ.filter fun i => s0 < (pins i).card).card * (s0 + 1) ≤
      ∑ i, (pins i).card := by
  classical
  let O := Finset.univ.filter fun i => s0 < (pins i).card
  calc
    O.card * (s0 + 1) = ∑ _i ∈ O, (s0 + 1) := by simp
    _ ≤ ∑ i ∈ O, (pins i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.succ_le_of_lt (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, (pins i).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Four times the tail exponent suffices to charge all discarded trials to collision rank. -/
theorem excessive_trials_exponent_le_rank {I J : Type*} [Fintype I] [DecidableEq I]
    (pins : I → Finset J) (s0 R rank : ℕ)
    (hbudget : 4 * R ≤ s0 + 1) (hcount : (∑ i, (pins i).card) ≤ 2 * rank) :
    2 * R * (Finset.univ.filter fun i => s0 < (pins i).card).card ≤ rank := by
  have hlarge := excessive_trials_count pins s0
  have hmul := Nat.mul_le_mul_left
    (Finset.univ.filter fun i => s0 < (pins i).card).card hbudget
  nlinarith

/-- The concrete pin budget has ample room for the coarser integral rank charge. -/
theorem pinBudget_rank_room (κ : CConsts) : 4 * κ.R ≤ ListGateContext.pinBudget κ + 1 := by
  have hceil := Nat.le_ceil (20 * (κ.R : ℝ))
  have hnat : 20 * κ.R ≤ ListGateContext.pinBudget κ := by
    unfold ListGateContext.pinBudget
    exact_mod_cast hceil
  omega

/-- The retained assertion depends only on the prescribed trial-pin labels. -/
theorem ownTrialCompatible_congr {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : D.F.Pool (D.G.cellOf v)) (pins : Finset (Pos T k))
    (fixed fixed' : Pos T k → Fin (T.S.N k))
    (h : ∀ w ∈ pins, fixed w = fixed' w) :
    ownTrialCompatible D v P pins fixed ↔ ownTrialCompatible D v P pins fixed' := by
  have hm : ∀ s, D.pinnedStatePriorMass v s pins fixed =
      D.pinnedStatePriorMass v s pins fixed' := by
    intro s
    unfold ListGateContext.pinnedStatePriorMass
    apply Finset.sum_congr rfl
    intro x hx
    congr 1
    exact Finset.prod_congr rfl (fun w hw => by rw [h w hw])
  simp only [ownTrialCompatible, hm]

/-- A positive actual slot weight certifies its prescribed label's permission. -/
theorem slot_weight_positive_permission {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (w : Pos T k)
    (P : D.F.Pool (D.G.cellOf w)) (j : Fin (D.G.nslot (D.G.cellOf w)))
    (y : Fin (T.S.N k)) (hw : 0 < externalSlotWeight D K hQuant w P j y) :
    y ∈ D.permittedLabels (D.G.cellOf w) P w := by
  have hslot : y ∈ (P j).1 ∧ hQuant.sampler.permittedBin w
      (cast (by rw [D.G.cellOf_patch]) (P j)) := by
    by_contra hn
    simp [externalSlotWeight, hn] at hw
  exact (hQuant.sampler.permission_present _ _ w rfl y).mpr ⟨j, hslot⟩

/-- Global compatibility supplies exactly the assertion retained by a sparse trial. -/
theorem compatible_pool_specialize {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (pools : D.PoolAssignment) (hc : D.compatiblePool v pools)
    (pins : Finset (Pos T k)) (hp : pins ⊆ D.externalEarly v)
    (hcard : pins.card ≤ ListGateContext.pinBudget κ)
    (fixed : Pos T k → Fin (T.S.N k))
    (hperm : ∀ w ∈ pins, fixed w ∈ D.permittedLabels (D.G.cellOf w)
      (pools (D.G.cellOf w)) w) :
    ownTrialCompatible D v (pools (D.G.cellOf v)) pins fixed :=
  hc pins hp hcard fixed hperm

/-- Conditioning a finite law is normalization of its weighted indicator. -/
theorem cond_E {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (S : Finset α) (hp : 0 < ∑ x ∈ S, P.w x) (f : α → ℝ) :
    (FinLaw.cond P S hp).E f = P.E (fun x => if x ∈ S then f x else 0) /
      (∑ x ∈ S, P.w x) := by
  classical
  unfold FinLaw.E
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hmem : x ∈ S <;> simp [FinLaw.cond, hmem] <;> ring

/-- One global slot pin preserves independence of all other physical-bin images. -/
theorem iid_pool_pin_flat_E {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hpools : (permPools D.G).Nonempty)
    (hB : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (pin : D.PoolPin) (hp : 0 < ∑ pools ∈ D.poolPinSet pin,
      (iidPoolLaw D.G hpools).w pools) (f : D.PoolAssignment → ℝ) :
    (FinLaw.cond (iidPoolLaw D.G hpools) (D.poolPinSet pin) hp).E f =
      (FinLaw.pi fun a : Σ C : D.G.Cell, Fin (D.G.nslot C) =>
        if ha : a = ⟨pin.cell, pin.slot⟩ then
          (ha.symm ▸ FinLaw.dirac pin.bin :
            FinLaw (Bin PT.tiling (D.G.cellPatch a.1)))
        else FinLaw.uniform Finset.univ (hB a.1)).E
          (fun z => f (fun C j => z ⟨C, j⟩)) := by
  classical
  let P := fun a : Σ C : D.G.Cell, Fin (D.G.nslot C) =>
    FinLaw.uniform Finset.univ (hB a.1)
  let S := Finset.univ.filter (fun z : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C),
    Bin PT.tiling (D.G.cellPatch a.1) => z ⟨pin.cell, pin.slot⟩ = pin.bin)
  have hMass : (∑ pools ∈ D.poolPinSet pin, (iidPoolLaw D.G hpools).w pools) =
      ∑ z ∈ S, (FinLaw.pi P).w z := by
    have h := iid_pool_flat_E D hpools hB
      (fun pools => if pools pin.cell pin.slot = pin.bin then (1 : ℝ) else 0)
    simpa [FinLaw.E, ListGateContext.poolPinSet, S, P, Finset.sum_filter] using h
  have hS : 0 < ∑ z ∈ S, (FinLaw.pi P).w z := hMass ▸ hp
  rw [cond_E, hMass]
  have hNum := iid_pool_flat_E D hpools hB
    (fun pools => if pools ∈ D.poolPinSet pin then f pools else 0)
  rw [hNum]
  have hCond := cond_E (FinLaw.pi P) S hS (fun z => f (fun C j => z ⟨C, j⟩))
  have hEvent : (fun z : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C),
      Bin PT.tiling (D.G.cellPatch a.1) =>
      if (fun C j => z ⟨C, j⟩) ∈ D.poolPinSet pin then f (fun C j => z ⟨C, j⟩) else 0) =
      fun z => if z ∈ S then f (fun C j => z ⟨C, j⟩) else 0 := by
    funext z
    simp [ListGateContext.poolPinSet, S]
  rw [hEvent, ← hCond]
  have hLaw := pi_condition_coordinate P ⟨pin.cell, pin.slot⟩ pin.bin hS
  simpa only [P, S] using congrArg
    (fun Q => Q.E (fun z => f (fun C j => z ⟨C, j⟩))) hLaw

/-- Pin weights and discarded-trial costs are absorbed by `121 * n` per rank. -/
theorem trial_rank_budget (n : ℝ) (hn : 1 ≤ n) (R m b q j : ℕ)
    (hb : b ≤ m) (hq : q ≤ 2 * j) (hloss : 2 * R * b ≤ j) :
    (11 : ℝ) ^ q * (2 / n ^ (2 * R)) ^ (m - b) ≤
      (2 / n ^ (2 * R)) ^ m * (121 * n) ^ j := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  let δ := 2 / n ^ (2 * R)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnp : n ^ (2 * R * b) ≤ n ^ j := pow_le_pow_right₀ hn hloss
  have htwo : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hcharge : 1 ≤ δ ^ b * n ^ j := by
    change 1 ≤ (2 / n ^ (2 * R)) ^ b * n ^ j
    rw [div_pow, ← pow_mul]
    have hden : 0 < n ^ (2 * R * b) := by positivity
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    simpa using hnp.trans (le_mul_of_one_le_left (by positivity) htwo)
  have htail : δ ^ (m - b) ≤ δ ^ m * n ^ j := by
    have heq : δ ^ (m - b) * δ ^ b = δ ^ m := by rw [← pow_add, Nat.sub_add_cancel hb]
    calc
      _ = δ ^ (m - b) * 1 := (mul_one _).symm
      _ ≤ δ ^ (m - b) * (δ ^ b * n ^ j) :=
        mul_le_mul_of_nonneg_left hcharge (pow_nonneg hδ.le _)
      _ = _ := by rw [← mul_assoc, heq]
  have hweight : (11 : ℝ) ^ q ≤ (121 : ℝ) ^ j := by
    calc
      _ ≤ (11 : ℝ) ^ (2 * j) := pow_le_pow_right₀ (by norm_num) hq
      _ = (121 : ℝ) ^ j := by rw [pow_mul]; norm_num
  calc
    _ ≤ (121 : ℝ) ^ j * (δ ^ m * n ^ j) :=
      mul_le_mul hweight htail (pow_nonneg hδ.le _) (by positivity)
    _ = _ := by rw [mul_pow]; dsimp [δ]; ring

/-- Expectations commute for two finite independent experiments. -/
theorem E_comm {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (f : α → β → ℝ) :
    P.E (fun a => Q.E (f a)) = Q.E (fun b => P.E (fun a => f a b)) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Raising a finite expectation to the number of independent trials introduces their product law. -/
theorem E_pow {α : Type*} [Fintype α] (P : FinLaw α) (f : α → ℝ) (m : ℕ) :
    (P.E f) ^ m = (FinLaw.pi fun _ : Fin m => P).E (fun z => ∏ i, f (z i)) := by
  rw [Lane_q_s17_pool.pi_expect_prod]
  simp

/-- A unique-coordinate integral can be bounded using only independent one-coordinate averages. -/
theorem unique_kernel_product_le {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (P : ∀ c, FinLaw (Ω c)) (e : I → C) (he : Function.Injective e)
    (W : ∀ i, Ω (e i) → ℝ) (π : I → ℝ)
    (hW : ∀ i z, 0 ≤ W i z) (hπ : ∀ i, (P (e i)).E (W i) ≤ π i) :
    (FinLaw.pi P).E (fun z => ∏ i, W i (z (e i))) ≤ ∏ i, π i := by
  rw [pi_E_injective_prod P e he W]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg (fun z _ => mul_nonneg ((P (e i)).nonneg z) (hW i z))
  · intro i hi
    exact hπ i

/-- Finite expectations distribute through an auxiliary finite sum. -/
theorem E_sum {α J : Type*} [Fintype α] [Fintype J] (P : FinLaw α)
    (f : J → α → ℝ) : P.E (fun z => ∑ j, f j z) = ∑ j, P.E (f j) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem E_const_mul {α : Type*} [Fintype α] (P : FinLaw α) (c : ℝ) (f : α → ℝ) :
    P.E (fun z => c * f z) = c * P.E f := by
  unfold FinLaw.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem E_mul_const {α : Type*} [Fintype α] (P : FinLaw α) (f : α → ℝ) (c : ℝ) :
    P.E (fun z => f z * c) = P.E f * c := by
  unfold FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Trial slot indices are sampled independently from their actual external cells. -/
noncomputable def trialSlotLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w)) :
    FinLaw (∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1))) :=
  FinLaw.pi fun w => FinLaw.uniform Finset.univ ⟨⟨0, hL w.1 w.2⟩, Finset.mem_univ _⟩

/-- The label-weight experiment after fixing one trial's actual slot indices. -/
noncomputable def slotTrialCost {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (pools : D.PoolAssignment)
    (slots : ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1))) : ℝ :=
  ∑ s : D.F.State (D.G.cellOf v), (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).w s *
    ∑ ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
      (∏ w, externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) (slots w) (ys w)) *
        if D.gateBad v (D.F.prior (D.G.cellOf v) s v)
          (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then 1 else 0

theorem slotTrialCost_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (pools : D.PoolAssignment)
    (slots : ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1))) :
    0 ≤ slotTrialCost D K hQuant v pools slots := by
  apply Finset.sum_nonneg
  intro s hs
  apply mul_nonneg ((D.F.fresh _ _).nonneg s)
  apply Finset.sum_nonneg
  intro ys hys
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun w _ => externalSlotWeight_nonneg D K hQuant _ _ _ _)
  · split_ifs <;> norm_num

/-- The singleton comparison is an expectation of the actual selected-slot experiment. -/
theorem fresh_le_slot_cost {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (pools : D.PoolAssignment) (htyp : D.LocalPoolsTypical v pools)
    (hodd : ∀ w ∈ D.externalEarly v, ¬ IsEvenRole w)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w)) :
    D.freshEventProbability v pools ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ (D.externalEarly v).card *
        (trialSlotLaw D v hL).E (slotTrialCost D K hQuant v pools) := by
  have h := fresh_star_slot_bound D K hQuant v heven pools htyp hodd hL
  convert h using 1
  congr 1
  unfold slotTrialCost
  rw [E_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [E_const_mul, E_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ys hys
  exact E_mul_const _ _ _

/-- The fixed-pool power is bounded by independent trials of the actual slot experiment. -/
theorem fresh_pow_le_slot_trials {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (pools : D.PoolAssignment) (htyp : D.LocalPoolsTypical v pools)
    (hodd : ∀ w ∈ D.externalEarly v, ¬ IsEvenRole w)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w)) (m : ℕ) :
    (D.freshEventProbability v pools) ^ m ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ ((D.externalEarly v).card * m) *
        (FinLaw.pi fun _ : Fin m => trialSlotLaw D v hL).E
          (fun slots => ∏ i, slotTrialCost D K hQuant v pools (slots i)) := by
  have hnonneg : 0 ≤ D.freshEventProbability v pools := by
    unfold ListGateContext.freshEventProbability FinLaw.pr
    exact Finset.sum_nonneg (fun s _ => by split_ifs; exact (D.freshConfigLaw pools).nonneg s; rfl)
  have h := pow_le_pow_left₀ hnonneg
    (fresh_le_slot_cost D K hQuant v heven pools htyp hodd hL) m
  rwa [mul_pow, ← pow_mul, E_pow] at h

/-- Occurrences whose slot is forced or visited more than once become trial pins. -/
noncomputable def trialPinOccurrences {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (e : I → A) (forced : Finset A) : Finset I :=
  Finset.univ.filter fun i => e i ∈ forced ∨
    2 ≤ (Finset.univ.filter fun j => e j = e i).card

/-- Every unpinned occurrence owns its slot uniquely among all occurrences. -/
theorem unique_occurrence_fiber {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (e : I → A) (forced : Finset A) (i : I)
    (hi : i ∉ trialPinOccurrences e forced) (j : I) (heq : e j = e i) : j = i := by
  classical
  have hnot : ¬ 2 ≤ (Finset.univ.filter fun j => e j = e i).card := by
    have h := hi
    simp only [trialPinOccurrences, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h
    exact h.2
  by_contra hne
  have hsub : ({i, j} : Finset I) ⊆ Finset.univ.filter (fun j => e j = e i) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with hzi | hzj
    · subst z; simp
    · have hzj' : z = j := Finset.mem_singleton.mp hzj
      subst z; simp [heq]
  have hc := Finset.card_le_card hsub
  have hcard : ({i, j} : Finset I).card = 2 := by simp [Ne.symm hne]
  rw [hcard] at hc
  exact hnot hc

theorem unique_occurrences_injective {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (e : I → A) (forced : Finset A) :
    Function.Injective (fun i : {i // i ∉ trialPinOccurrences e forced} => e i.1) := by
  intro i j h
  apply Subtype.ext
  exact unique_occurrence_fiber e forced j.1 j.2 i.1 h

theorem pinned_image_not_unique {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (e : I → A) (forced : Finset A) (i : I)
    (hi : i ∈ trialPinOccurrences e forced) :
    e i ∉ (Finset.univ \ trialPinOccurrences e forced).image e := by
  rintro h
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
  have hj' := (Finset.mem_sdiff.mp hj).2
  have hij : i = j := unique_occurrence_fiber e forced j hj' i heq.symm
  exact hj' (hij ▸ hi)

theorem forced_not_unique_image {I A : Type*} [Fintype I] [DecidableEq I]
    [DecidableEq A] (e : I → A) (forced : Finset A) (a : A) (ha : a ∈ forced) :
    a ∉ (Finset.univ \ trialPinOccurrences e forced).image e := by
  rintro h
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp h
  apply (Finset.mem_sdiff.mp hi).2
  simp [trialPinOccurrences, heq, ha]

/-- Partition the bad occurrence set by its trial coordinate. -/
noncomputable def trialPins {I J : Type*} [Fintype J] [DecidableEq I] [DecidableEq J]
    (B : Finset (I × J)) (i : I) : Finset J := Finset.univ.filter fun j => (i, j) ∈ B

theorem trialPins_sum {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (B : Finset (I × J)) :
    (∑ i, (trialPins B i).card) = B.card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter B Finset.univ Prod.fst
  have hcard (i : I) : (B.filter fun a => a.1 = i).card = (trialPins B i).card := by
    apply Finset.card_bij (fun a _ => a.2)
    · intro a ha
      obtain ⟨haB, hai⟩ := Finset.mem_filter.mp ha
      simpa [trialPins, ← hai] using haB
    · intro a ha b hb hab
      apply Prod.ext
      · exact (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
      · exact hab
    · intro j hj
      refine ⟨(i, j), ?_, rfl⟩
      simpa [trialPins] using hj
  simpa [hcard] using h

/-- The collision-rank charge for discarded trials, directly for trial-pin occurrences. -/
theorem trialPins_loss_le_rank {I J A : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [DecidableEq A]
    (e : I × J → A) (forced : Finset A) (R s0 rank : ℕ)
    (hbudget : 4 * R ≤ s0 + 1)
    (hrank : Fintype.card (I × J) - ((Finset.univ.image e) \ forced).card = rank) :
    2 * R * (Finset.univ.filter fun i =>
      s0 < (trialPins (trialPinOccurrences e forced) i).card).card ≤ rank := by
  apply excessive_trials_exponent_le_rank _ s0 R rank hbudget
  rw [trialPins_sum]
  have h := nonunique_occurrences_le_two_rank e forced
  rw [hrank] at h
  simpa only [trialPinOccurrences] using h

/-- A coordinate-weight sum after fixing all shared images is controlled by its
independent singleton averages and the remaining sparse-trial tail estimates. -/
theorem shared_slot_integral_bound {I J C α : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype C] [DecidableEq C] [Fintype α]
    {Ω : C → Type*} [∀ c, Fintype (Ω c)]
    (P : ∀ c, FinLaw (Ω c)) (π : J → FinLaw α)
    (e : I × J → C) (B : Finset (I × J))
    (W : ∀ o : I × J, Ω (e o) → α → ℝ)
    (f : (∀ c, Ω c) → I → (J → α) → ℝ) (base : α)
    (c : ℝ) (δ : I → ℝ) (hc : 0 ≤ c) (hδ : ∀ i, 0 ≤ δ i)
    (hW : ∀ o z y, 0 ≤ W o z y)
    (hmass : ∀ o z, (∑ y, W o z y) ≤ c)
    (hf : ∀ z i ys, 0 ≤ f z i ys)
    (hInject : ∀ o ∉ B, ∀ o', e o' = e o → o' = o)
    (hAverage : ∀ o ∉ B, ∀ y, (P (e o)).E (fun z => W o z y) ≤ (π o.2).w y)
    (hlocal : ∀ z z', (∀ a, a ∉ (Finset.univ \ B).image e → z a = z' a) →
      ∀ i ys, f z i ys = f z' i ys)
    (htrial : ∀ z i (fixed : {j // j ∈ trialPins B i} → α),
      (FinLaw.pi fun j => if hj : j ∈ trialPins B i then FinLaw.dirac (fixed ⟨j, hj⟩)
        else π j).E (f z i) ≤ δ i) :
    (FinLaw.pi P).E (fun z =>
      ∑ ys : I → J → α, (∏ o : I × J, W o (z (e o)) (ys o.1 o.2)) *
        ∏ i, f z i (ys i)) ≤ c ^ B.card * ∏ i, δ i := by
  classical
  let U := Finset.univ \ B
  let S := U.image e
  let z0 : ∀ a, Ω a := Classical.choice (nonempty_of_finLaw (FinLaw.pi P))
  rw [pi_E_split P S]
  have hInner : ∀ outside : ∀ a : {a // a ∉ S}, Ω a.1,
      (FinLaw.pi fun a : {a // a ∈ S} => P a.1).E (fun inside =>
        let z := fun a => if ha : a ∈ S then inside ⟨a, ha⟩ else outside ⟨a, ha⟩
        ∑ ys : I → J → α, (∏ o : I × J, W o (z (e o)) (ys o.1 o.2)) *
          ∏ i, f z i (ys i)) ≤ c ^ B.card * ∏ i, δ i := by
    intro outside
    let zbase : ∀ a, Ω a := fun a => if ha : a ∈ S then z0 a else outside ⟨a, ha⟩
    let patch := fun (inside : ∀ a : {a // a ∈ S}, Ω a.1) (a : C) =>
      if ha : a ∈ S then inside ⟨a, ha⟩ else outside ⟨a, ha⟩
    have hout (inside : ∀ a : {a // a ∈ S}, Ω a.1) (a : C) (ha : a ∉ S) :
        patch inside a = zbase a := by simp [patch, zbase, ha]
    have hbad (o : I × J) (ho : o ∈ B) : e o ∉ S := by
      intro hs
      obtain ⟨u, hu, heu⟩ := Finset.mem_image.mp hs
      have huB : u ∉ B := (Finset.mem_sdiff.mp hu).2
      have hou := hInject u huB o heu.symm
      exact huB (hou ▸ ho)
    have hF (inside : ∀ a : {a // a ∈ S}, Ω a.1) (i : I) (ys : J → α) :
        f (patch inside) i ys = f zbase i ys :=
      hlocal _ _ (fun a ha => hout inside a ha) i ys
    let eu : {o // o ∈ U} → {a // a ∈ S} := fun o =>
      ⟨e o.1, Finset.mem_image.mpr ⟨o.1, o.2, rfl⟩⟩
    have heu : Function.Injective eu := by
      intro u v huv
      apply Subtype.ext
      apply hInject v.1 (Finset.mem_sdiff.mp v.2).2 u.1
      exact congrArg Subtype.val huv
    rw [E_sum]
    have hrow : ∀ ys : I → J → α,
        (FinLaw.pi fun a : {a // a ∈ S} => P a.1).E (fun inside =>
          (∏ o : I × J, W o (patch inside (e o)) (ys o.1 o.2)) *
            ∏ i, f (patch inside) i (ys i)) ≤
          (∏ i, ∏ j, if j ∈ trialPins B i then W (i, j) (zbase (e (i, j))) (ys i j)
            else (π j).w (ys i j)) * ∏ i, f zbase i (ys i) := by
      intro ys
      have hsplit (inside : ∀ a : {a // a ∈ S}, Ω a.1) :
          (∏ o : I × J, W o (patch inside (e o)) (ys o.1 o.2)) =
            (∏ o ∈ B, W o (zbase (e o)) (ys o.1 o.2)) *
              ∏ o : {o // o ∈ U}, W o.1 (inside (eu o)) (ys o.1.1 o.1.2) := by
        calc
          _ = (∏ o ∈ B, W o (patch inside (e o)) (ys o.1 o.2)) *
              ∏ o ∈ U, W o (patch inside (e o)) (ys o.1 o.2) := by
            simpa [U, Finset.compl_eq_univ_sdiff] using
              (Finset.prod_mul_prod_compl B (fun o => W o (patch inside (e o)) (ys o.1 o.2))).symm
          _ = _ := by
            congr 1
            · exact Finset.prod_congr rfl (fun o ho => by rw [hout inside _ (hbad o ho)])
            · rw [Finset.prod_subtype U (fun _ => Iff.rfl)]
              apply Finset.prod_congr rfl
              intro o ho
              dsimp only [patch]
              rw [dif_pos (show e o.1 ∈ S from (eu o).2)]
      have hAverageU := unique_kernel_product_le
        (fun a : {a // a ∈ S} => P a.1) eu heu
        (fun o z => W o.1 z (ys o.1.1 o.1.2))
        (fun o => (π o.1.2).w (ys o.1.1 o.1.2))
        (fun o z => hW o.1 z _) (fun o => hAverage o.1 (Finset.mem_sdiff.mp o.2).2 _)
      have hRewrite : (fun inside : ∀ a : {a // a ∈ S}, Ω a.1 =>
          (∏ o : I × J, W o (patch inside (e o)) (ys o.1 o.2)) *
            ∏ i, f (patch inside) i (ys i)) = fun inside =>
          (∏ o ∈ B, W o (zbase (e o)) (ys o.1 o.2)) *
            (∏ o : {o // o ∈ U}, W o.1 (inside (eu o)) (ys o.1.1 o.1.2)) *
              ∏ i, f zbase i (ys i) := by
        funext inside
        rw [hsplit]
        simp_rw [hF]
      rw [hRewrite, E_mul_const, E_const_mul]
      have hB0 : 0 ≤ ∏ o ∈ B, W o (zbase (e o)) (ys o.1 o.2) :=
        Finset.prod_nonneg (fun o _ => hW o (zbase (e o)) (ys o.1 o.2))
      have hF0 : 0 ≤ ∏ i, f zbase i (ys i) :=
        Finset.prod_nonneg (fun i _ => hf zbase i (ys i))
      have hBounds := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAverageU hB0) hF0
      convert hBounds using 1
      have hSub : (∏ o ∈ U, (π o.2).w (ys o.1 o.2)) =
          ∏ o : {o // o ∈ U}, (π o.1.2).w (ys o.1.1 o.1.2) :=
        Finset.prod_subtype (F := inferInstance) U (fun _ => Iff.rfl) _
      rw [← hSub]
      have hpartition : (∏ o ∈ B, W o (zbase (e o)) (ys o.1 o.2)) *
          (∏ o ∈ U, (π o.2).w (ys o.1 o.2)) =
          ∏ o : I × J, if o ∈ B then W o (zbase (e o)) (ys o.1 o.2)
            else (π o.2).w (ys o.1 o.2) := by
        simpa [U, Finset.sdiff_eq_filter, Finset.filter_mem_eq_inter] using
          (Finset.prod_ite (s := Finset.univ) (p := fun o => o ∈ B)
            (fun o => W o (zbase (e o)) (ys o.1 o.2))
            (fun o => (π o.2).w (ys o.1 o.2))).symm
      rw [hpartition, Fintype.prod_prod_type]
      simp only [trialPins, Finset.mem_filter, Finset.mem_univ, true_and]
    calc
      _ ≤ ∑ ys : I → J → α,
          (∏ i, ∏ j, if j ∈ trialPins B i then W (i, j) (zbase (e (i, j))) (ys i j)
            else (π j).w (ys i j)) * ∏ i, f zbase i (ys i) :=
        Finset.sum_le_sum (fun ys _ => hrow ys)
      _ ≤ c ^ (∑ i, (trialPins B i).card) * ∏ i, δ i :=
        sparse_trial_product_bound π (trialPins B) (fun i j => W (i, j) (zbase (e (i, j))))
          base (f zbase) c δ hc hδ (fun i j => hW (i, j) _) (fun i j _ => hmass (i, j) _)
          (hf zbase) (htrial zbase)
      _ = _ := by rw [trialPins_sum]
  calc
    _ ≤ (FinLaw.pi fun a : {a // a ∉ S} => P a.1).E
        (fun _ => c ^ B.card * ∏ i, δ i) := by
      apply Finset.sum_le_sum
      intro outside ho
      exact mul_le_mul_of_nonneg_left (hInner outside) ((FinLaw.pi _).nonneg outside)
    _ = c ^ B.card * ∏ i, δ i := by
      unfold FinLaw.E
      rw [← Finset.sum_mul, (FinLaw.pi _).sum_one, one_mul]

/-- A predicate reading only pinned labels can be retained before integrating unique labels. -/
theorem pinned_pi_E_test {I α : Type*} [Fintype I] [DecidableEq I] [Fintype α]
    (P : I → FinLaw α) (S : Finset I) (fixed : I → α)
    (A : (I → α) → Prop) (f : (I → α) → ℝ)
    (hA : ∀ ys, (∀ i ∈ S, ys i = fixed i) → (A ys ↔ A fixed)) :
    (FinLaw.pi fun i => if i ∈ S then FinLaw.dirac (fixed i) else P i).E
      (fun ys => if A ys then f ys else 0) =
      if A fixed then (FinLaw.pi fun i => if i ∈ S then FinLaw.dirac (fixed i) else P i).E f else 0 := by
  classical
  rw [pinned_pi_E]
  have hpoint (outside : {i // i ∉ S} → α) :
      A (fun i => if hi : i ∈ S then fixed i else outside ⟨i, hi⟩) ↔ A fixed :=
    hA _ (fun i hi => by simp [hi])
  simp_rw [hpoint]
  by_cases h : A fixed
  · simp only [h, ite_true]
    exact (pinned_pi_E P S fixed f).symm
  · simp [h, FinLaw.E]

/-- The own-tape compatibility restriction is evaluated before any unpinned label is integrated. -/
theorem retained_sparse_trial_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (P : D.F.Pool (D.G.cellOf v))
    (pins : Finset (Pos T k)) (hpins : pins ⊆ D.externalEarly v)
    (fixed : Pos T k → Fin (T.S.N k))
    (hEstimate : ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤ D.pinnedPriorMass v σ pins fixed →
      (D.pinnedLabelLaw v pins fixed).pr
        (fun ys => D.gateBad v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
          Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))) :
    (D.pinnedLabelLaw v pins fixed).E (fun ys =>
      if D.F.typical (D.G.cellOf v) P ∧
          ownTrialCompatible D v P pins (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then
        (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
          D.gateBad v (D.F.prior (D.G.cellOf v) s v)
            (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) else 0) ≤
      2 * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  classical
  let S : Finset {w : Pos T k // w ∈ D.externalEarly v} :=
    Finset.univ.filter fun w => w.1 ∈ pins
  let fixedE : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k) := fun w => fixed w.1
  let A := fun ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k) =>
    D.F.typical (D.G.cellOf v) P ∧
      ownTrialCompatible D v P pins (D.labelsOfPinnedSample v (T.S.N_pos k) ys)
  let g := fun ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k) =>
    (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
      D.gateBad v (D.F.prior (D.G.cellOf v) s v)
        (D.labelsOfPinnedSample v (T.S.N_pos k) ys))
  have hA : ∀ ys, (∀ w ∈ S, ys w = fixedE w) → (A ys ↔ A fixedE) := by
    intro ys hy
    dsimp [A]
    apply and_congr_right'
    apply ownTrialCompatible_congr
    intro w hw
    have he := hpins hw
    simpa [ListGateContext.labelsOfPinnedSample, he, fixedE] using
      hy ⟨w, he⟩ (by simp [S, hw])
  change (D.pinnedLabelLaw v pins fixed).E (fun ys => if A ys then g ys else 0) ≤ _
  have hSupport : ∀ ys, (D.pinnedLabelLaw v pins fixed).w ys ≠ 0 → (A ys ↔ A fixedE) := by
    intro ys hy
    apply hA ys
    intro w hw
    have hwpins : w.1 ∈ pins := (Finset.mem_filter.mp hw).2
    by_contra hne
    apply hy
    unfold ListGateContext.pinnedLabelLaw
    change (∏ z, (if z.1 ∈ pins then FinLaw.dirac (fixed z.1)
      else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf z.1))).w (ys z)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ w)
    simp only [hwpins, ite_true, FinLaw.dirac]
    exact if_neg hne
  have hTest' : (D.pinnedLabelLaw v pins fixed).E (fun ys => if A ys then g ys else 0) =
      if A fixedE then (D.pinnedLabelLaw v pins fixed).E g else 0 := by
    by_cases ha : A fixedE
    · simp only [ha, ite_true]
      unfold FinLaw.E
      apply Finset.sum_congr rfl
      intro ys hys
      by_cases hz : (D.pinnedLabelLaw v pins fixed).w ys = 0
      · simp [hz]
      · simp [(hSupport ys hz).mpr ha]
    · simp only [ha, ite_false]
      unfold FinLaw.E
      apply Finset.sum_eq_zero
      intro ys hys
      by_cases hz : (D.pinnedLabelLaw v pins fixed).w ys = 0
      · simp [hz]
      · have hnot : ¬ A ys := fun h => ha ((hSupport ys hz).mp h)
        simp [hnot]
  rw [hTest']
  by_cases ha : A fixedE
  · simp only [ha, ite_true]
    have hc : ownTrialCompatible D v P pins fixed := by
      apply (ownTrialCompatible_congr D v P pins
        (D.labelsOfPinnedSample v (T.S.N_pos k) fixedE) fixed (fun w hw => by
        simp [ListGateContext.labelsOfPinnedSample, hpins hw, fixedE])).mp
      exact ha.2
    have hb := own_compatible_sparse_trial D K hQuant v heven P ha.1 pins fixed hc hEstimate
    rw [Lane_sol_s17_pool.bind_pr] at hb
    have heq : (D.pinnedLabelLaw v pins fixed).E g =
        (D.F.fresh (D.G.cellOf v) P).E (fun s =>
          (D.pinnedLabelLaw v pins fixed).pr (fun ys =>
            D.gateBad v (D.F.prior (D.G.cellOf v) s v)
              (D.labelsOfPinnedSample v (T.S.N_pos k) ys))) := by
      dsimp only [g]
      unfold FinLaw.E FinLaw.pr
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro ys hys
      by_cases hbad : D.gateBad v (D.F.prior (D.G.cellOf v) s v)
        (D.labelsOfPinnedSample v (T.S.N_pos k) ys) <;> simp [hbad, mul_comm]
    rw [heq]
    exact hb
  · simp only [ha, ite_false]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The accumulated singleton and iid comparison errors cost at most two for `m ≤ n`. -/
theorem comparison_errors_le_two (n : ℝ) (hn : 4 ≤ n) (d m : ℕ)
    (hd : (d : ℝ) ≤ n) (hm : (m : ℝ) ≤ n) :
    (1 + 1 / n ^ 3) ^ (d * m + 1) ≤ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn1
  have hcount : ((d * m + 1 : ℕ) : ℝ) ≤ 2 * n ^ 2 := by
    have hp := mul_le_mul hd hm (Nat.cast_nonneg m) hn0.le
    push_cast
    nlinarith
  have hexponent : ((d * m + 1 : ℕ) : ℝ) * (1 / n ^ 3) ≤ 1 / 2 := by
    calc
      _ ≤ (2 * n ^ 2) * (1 / n ^ 3) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = 2 / n := by field_simp <;> ring
      _ ≤ 1 / 2 := by apply (div_le_iff₀ hn0).mpr; linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  calc
    _ ≤ (Real.exp (1 / n ^ 3)) ^ (d * m + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (1 / n ^ 3)
    _ = Real.exp (((d * m + 1 : ℕ) : ℝ) * (1 / n ^ 3)) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (hexponent.trans hlog)
    _ = 2 := Real.exp_log (by norm_num)

/-- The stronger sparse tail absorbs every comparison error before the rank sum. -/
theorem comparison_tail_budget (n : ℝ) (hn : 4 ≤ n) (R d m : ℕ)
    (hR : 1 ≤ R) (hm1 : 1 ≤ m) (hd : (d : ℝ) ≤ n) (hm : (m : ℝ) ≤ n) :
    (1 + 1 / n ^ 3) ^ (d * m + 1) * (2 / n ^ (2 * R)) ^ m ≤
      1 / n ^ (R * m) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hpower : (4 : ℝ) ≤ n ^ R := by
    calc
      _ ≤ n := hn
      _ = n ^ 1 := (pow_one _).symm
      _ ≤ n ^ R := pow_le_pow_right₀ hn1 hR
  have htwopower : 2 * (2 : ℝ) ^ m ≤ n ^ (R * m) := by
    calc
      _ ≤ (2 : ℝ) ^ m * 2 ^ m :=
        mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm1)
          (by positivity)
      _ = (4 : ℝ) ^ m := by rw [← mul_pow]; norm_num
      _ ≤ (n ^ R) ^ m := pow_le_pow_left₀ (by norm_num) hpower m
      _ = _ := (pow_mul _ _ _).symm
  calc
    _ ≤ 2 * (2 / n ^ (2 * R)) ^ m :=
      mul_le_mul_of_nonneg_right (comparison_errors_le_two n hn d m hd hm) (by positivity)
    _ = (2 * (2 : ℝ) ^ m) / (n ^ (R * m)) ^ 2 := by
      rw [div_pow, ← pow_mul, ← pow_mul]
      have he : (2 * R) * m = (R * m) * 2 := by ring
      rw [he]
      ring
    _ ≤ n ^ (R * m) / (n ^ (R * m)) ^ 2 :=
      div_le_div_of_nonneg_right htwopower (by positivity)
    _ = _ := by field_simp <;> ring

/-- `⌈log² n⌉` is eventually at most `n`, uniformly before selecting a context. -/
theorem rounds_eventually_le_n (T : Stage) :
    ∀ᶠ k in Filter.atTop, initialResamplingRounds T k ≤ T.S.n k := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (by norm_num : (0 : ℝ) < 1)
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  filter_upwards [hn.eventually h] with k hk
  apply Nat.ceil_le.mpr
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (T.S.n k : ℝ))),
    abs_of_nonneg (Nat.cast_nonneg (T.S.n k) : (0 : ℝ) ≤ T.S.n k), id_eq, one_mul] using hk

/-- A tenth-power slot lower bound already suffices for the coarse rank budget. -/
theorem collision_rank_moment_two {A : Type*} [Fintype A] [DecidableEq A]
    (n : ℝ) (hn : 10 ≤ n) (q : ℕ) (hq : (q : ℝ) ≤ n ^ 2)
    (P : Fin q → FinLaw A) (forced : Finset A) (hforced : forced.card ≤ 1)
    (hP : ∀ i a, (P i).w a ≤ 1 / n ^ 10) :
    (FinLaw.pi P).E (fun z => (121 * n) ^ repeatRank q forced z) ≤ 2 := by
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hn2 : 1 ≤ n ^ 2 := one_le_pow₀ hn1
  have hM : ((q + 1 : ℕ) : ℝ) ≤ 2 * n ^ 2 := by push_cast; linarith
  have hsmall : (q : ℝ) * (((q + 1 : ℕ) : ℝ) * (121 * n) / n ^ 10) ≤ Real.log 2 := by
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      linarith
    calc
      _ = ((q : ℝ) * ((q + 1 : ℕ) : ℝ) * (121 * n)) / n ^ 10 := by ring
      _ ≤ (n ^ 2 * (2 * n ^ 2) * (121 * n)) / n ^ 10 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        gcongr
      _ = 242 / n ^ 5 := by field_simp <;> ring
      _ ≤ 242 / (10 : ℝ) ^ 5 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        exact pow_le_pow_left₀ (by norm_num) hn 5
      _ ≤ 1 / 2 := by norm_num
      _ ≤ _ := hlog
  exact independent_repeat_rank_moment_two (q + 1) q (n ^ 10) (121 * n)
    (by positivity) (by nlinarith) P forced (by omega) hP hsmall

/-- External-subtype trial pins as actual cube positions. -/
noncomputable def positionPins {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (S : Finset {w : Pos T k // w ∈ D.externalEarly v}) : Finset (Pos T k) :=
  S.image Subtype.val

theorem positionPins_card {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (S : Finset {w : Pos T k // w ∈ D.externalEarly v}) :
    (positionPins D v S).card = S.card :=
  Finset.card_image_of_injective S Subtype.val_injective

theorem positionPins_subset {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (S : Finset {w : Pos T k // w ∈ D.externalEarly v}) :
    positionPins D v S ⊆ D.externalEarly v := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
  exact z.2

theorem positionPins_mem {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (S : Finset {w : Pos T k // w ∈ D.externalEarly v})
    (w : {w : Pos T k // w ∈ D.externalEarly v}) :
    w.1 ∈ positionPins D v S ↔ w ∈ S := by
  constructor
  · intro h
    obtain ⟨z, hz, hzw⟩ := Finset.mem_image.mp h
    have hzw' : z = w := Subtype.ext hzw
    exact hzw' ▸ hz
  · exact fun h => Finset.mem_image_of_mem _ h

/-- The trial predicate retained from the original compatible, typical pool indicator. -/
noncomputable def retainedTrialTest {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : D.F.Pool (D.G.cellOf v))
    (pins : Finset {w : Pos T k // w ∈ D.externalEarly v})
    (ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) : ℝ :=
  if D.F.typical (D.G.cellOf v) P ∧
      (pins.card ≤ ListGateContext.pinBudget κ → ownTrialCompatible D v P
        (positionPins D v pins) (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) then
    (D.F.fresh (D.G.cellOf v) P).pr (fun s => D.gateBad v (D.F.prior (D.G.cellOf v) s v)
      (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) else 0

theorem retainedTrialTest_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : D.F.Pool (D.G.cellOf v))
    (pins : Finset {w : Pos T k // w ∈ D.externalEarly v})
    (ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :
    0 ≤ retainedTrialTest D v P pins ys := by
  unfold retainedTrialTest
  split_ifs
  · unfold FinLaw.pr
    exact Finset.sum_nonneg (fun s _ => by split_ifs; exact (D.F.fresh _ _).nonneg s; rfl)
  · rfl

theorem retainedTrialTest_le_one {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k)
    (P : D.F.Pool (D.G.cellOf v))
    (pins : Finset {w : Pos T k // w ∈ D.externalEarly v})
    (ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :
    retainedTrialTest D v P pins ys ≤ 1 := by
  unfold retainedTrialTest
  split_ifs
  · exact probability_le_one _ _
  · norm_num

/-- The independent pinned-label input, specialized to the current even star. -/
def StarPinnedEstimate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT) (v : Pos T k) : Prop :=
  ∀ (pins : Finset (Pos T k)), pins ⊆ D.externalEarly v →
    pins.card ≤ ListGateContext.pinBudget κ → ∀ (fixed : Pos T k → Fin (T.S.N k))
      (σ : Fin (T.S.N k) → ℝ), D.ValidInitialPrior v σ →
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤ D.pinnedPriorMass v σ pins fixed →
      (D.pinnedLabelLaw v pins fixed).pr
        (fun ys => D.gateBad v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
          Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))

/-- Sparse retained trials pay two tail budgets; overfull retained trials pay one. -/
theorem retainedTrialTest_pinned_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (hEstimate : StarPinnedEstimate D v)
    (P : D.F.Pool (D.G.cellOf v))
    (S : Finset {w : Pos T k // w ∈ D.externalEarly v})
    (fixed : {w // w ∈ S} → Fin (T.S.N k)) :
    (FinLaw.pi fun w : {w : Pos T k // w ∈ D.externalEarly v} =>
      if hw : w ∈ S then FinLaw.dirac (fixed ⟨w, hw⟩)
      else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))).E
        (retainedTrialTest D v P S) ≤
      if S.card ≤ ListGateContext.pinBudget κ then
        2 * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) else 1 := by
  classical
  by_cases hS : S.card ≤ ListGateContext.pinBudget κ
  · simp only [hS, ite_true]
    let allfixed : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k) :=
      fun w => if hw : w ∈ S then fixed ⟨w, hw⟩ else ⟨0, T.S.N_pos k⟩
    let fp := D.labelsOfPinnedSample v (T.S.N_pos k) allfixed
    let pins := positionPins D v S
    let Q : FinLaw ({w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :=
      FinLaw.pi fun w => if hw : w ∈ S then FinLaw.dirac (fixed ⟨w, hw⟩)
        else ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))
    have hLaw : Q = D.pinnedLabelLaw v pins fp := by
      dsimp only [Q]
      unfold ListGateContext.pinnedLabelLaw
      congr 1
      funext w
      have hmem : w.1 ∈ pins ↔ w ∈ S := positionPins_mem D v S w
      simp only [hmem]
      by_cases hw : w ∈ S
      · simp [hw, fp, ListGateContext.labelsOfPinnedSample, w.2, allfixed]
      · simp [hw]
    have hCard : pins.card ≤ ListGateContext.pinBudget κ := by
      simpa [pins, positionPins_card] using hS
    have hBound := retained_sparse_trial_bound D K hQuant v heven P pins
      (positionPins_subset D v S) fp (hEstimate pins (positionPins_subset D v S) hCard fp)
    have hfun : retainedTrialTest D v P S = fun ys =>
        if D.F.typical (D.G.cellOf v) P ∧ ownTrialCompatible D v P pins
          (D.labelsOfPinnedSample v (T.S.N_pos k) ys) then
          (D.F.fresh (D.G.cellOf v) P).pr (fun s =>
            D.gateBad v (D.F.prior (D.G.cellOf v) s v)
              (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) else 0 := by
      funext ys
      simp [retainedTrialTest, hS, pins]
    have hEq := congrArg (fun L => L.E (retainedTrialTest D v P S)) hLaw
    change Q.E (retainedTrialTest D v P S) ≤ _
    rw [hEq, hfun]
    exact hBound
  · simp only [hS, ite_false]
    calc
      _ ≤ ∑ ys, (FinLaw.pi _).w ys * 1 := by
        apply Finset.sum_le_sum
        intro ys hys
        exact mul_le_mul_of_nonneg_left (retainedTrialTest_le_one D v P S ys)
          ((FinLaw.pi _).nonneg ys)
      _ = 1 := by simp [FinLaw.sum_one]

/-- Reorder the actual one-trial cost to put its own-tape probability inside the label sum. -/
theorem slotTrialCost_label_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (pools : D.PoolAssignment)
    (slots : ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1))) :
    slotTrialCost D K hQuant v pools slots =
      ∑ ys : {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
        (∏ w, externalSlotWeight D K hQuant w.1 (pools (D.G.cellOf w.1)) (slots w) (ys w)) *
          (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
            D.gateBad v (D.F.prior (D.G.cellOf v) s v)
              (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) := by
  unfold slotTrialCost FinLaw.pr
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ys hys
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : D.gateBad v (D.F.prior (D.G.cellOf v) s v)
    (D.labelsOfPinnedSample v (T.S.N_pos k) ys) <;> simp [h, mul_comm]

/-- Positive selected-slot weights let the actual compatible-pool indicator be
weakened to the own-tape assertion of each sparse trial. -/
theorem compatible_weighted_trials_retained {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (m : ℕ) (pools : D.PoolAssignment)
    (slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v},
      Fin (D.G.nslot (D.G.cellOf w.1)))
    (B : Finset (Fin m × {w : Pos T k // w ∈ D.externalEarly v}))
    (ys : Fin m → {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k)) :
    (if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then (1 : ℝ) else 0) *
      (∏ o : Fin m × {w : Pos T k // w ∈ D.externalEarly v},
        externalSlotWeight D K hQuant o.2.1 (pools (D.G.cellOf o.2.1))
          (slots o.1 o.2) (ys o.1 o.2)) *
        (∏ i, (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
          D.gateBad v (D.F.prior (D.G.cellOf v) s v)
            (D.labelsOfPinnedSample v (T.S.N_pos k) (ys i)))) ≤
      (∏ o : Fin m × {w : Pos T k // w ∈ D.externalEarly v},
        externalSlotWeight D K hQuant o.2.1 (pools (D.G.cellOf o.2.1))
          (slots o.1 o.2) (ys o.1 o.2)) *
        ∏ i, retainedTrialTest D v (pools (D.G.cellOf v)) (trialPins B i) (ys i) := by
  classical
  let W := fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
    externalSlotWeight D K hQuant o.2.1 (pools (D.G.cellOf o.2.1))
      (slots o.1 o.2) (ys o.1 o.2)
  have hW : ∀ o, 0 ≤ W o := fun o => externalSlotWeight_nonneg D K hQuant _ _ _ _
  have hRet0 : 0 ≤ ∏ i, retainedTrialTest D v (pools (D.G.cellOf v)) (trialPins B i) (ys i) :=
    Finset.prod_nonneg (fun i _ => retainedTrialTest_nonneg D v _ _ _)
  by_cases hg : D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools
  · rw [if_pos hg, one_mul]
    by_cases hz : (∏ o, W o) = 0
    · change (∏ o, W o) * _ ≤ (∏ o, W o) * _
      simp [hz]
    · have hpos (o) : 0 < W o := by
        apply lt_of_le_of_ne (hW o)
        intro heq
        exact hz (Finset.prod_eq_zero (Finset.mem_univ o) heq.symm)
      have hretain (i : Fin m) : retainedTrialTest D v (pools (D.G.cellOf v)) (trialPins B i) (ys i) =
          (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
            D.gateBad v (D.F.prior (D.G.cellOf v) s v)
              (D.labelsOfPinnedSample v (T.S.N_pos k) (ys i))) := by
        have htyp : D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)) :=
          hg.1 _ (by simp [ListGateContext.scopeCells])
        have hc : (trialPins B i).card ≤ ListGateContext.pinBudget κ →
            ownTrialCompatible D v (pools (D.G.cellOf v)) (positionPins D v (trialPins B i))
              (D.labelsOfPinnedSample v (T.S.N_pos k) (ys i)) := by
          intro hcard
          apply compatible_pool_specialize D v pools hg.2 _ (positionPins_subset D v _)
            (by simpa [positionPins_card] using hcard)
          intro w hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          have hperm := slot_weight_positive_permission D K hQuant z.1
            (pools (D.G.cellOf z.1)) (slots i z) (ys i z) (hpos (i, z))
          simpa [ListGateContext.labelsOfPinnedSample, z.2] using hperm
        exact if_pos ⟨htyp, hc⟩
      simp_rw [hretain]
      exact le_refl _
  · simp only [hg, ite_false, zero_mul]
    exact mul_nonneg (Finset.prod_nonneg (fun o _ => hW o)) hRet0

/-- Actual permission-weighted label kernel of one physical bin image. -/
noncomputable def binLabelWeight {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (w : Pos T k)
    (B : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w))) (y : Fin (T.S.N k)) : ℝ :=
  (Fintype.card (Bin PT.tiling (D.G.patchOf w)) : ℝ) * (PT.π (D.G.patchOf w)).w y *
    if y ∈ B.1 ∧ hQuant.sampler.permittedBin w
      (cast (by rw [D.G.cellOf_patch]) B) then 1 else 0

theorem binLabelWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (w : Pos T k)
    (B : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w))) (y : Fin (T.S.N k)) :
    0 ≤ binLabelWeight D K hQuant w B y := by
  unfold binLabelWeight
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ((PT.π _).nonneg _))
    (by split_ifs <;> norm_num)

theorem binLabelWeight_total {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (w : Pos T k)
    (B : Bin PT.tiling (D.G.cellPatch (D.G.cellOf w)))
    (hL : 0 < D.G.nslot (D.G.cellOf w)) :
    (∑ y, binLabelWeight D K hQuant w B y) ≤ 11 :=
  externalSlotWeight_total_le_eleven D K hQuant w (fun _ => B) ⟨0, hL⟩

/-- Integrating an unforced physical bin restores the independent comparison prior. -/
theorem binLabelWeight_average {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (w : Pos T k)
    (hB : (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch (D.G.cellOf w)))).Nonempty)
    (y : Fin (T.S.N k)) :
    (FinLaw.uniform Finset.univ hB).E (fun B => binLabelWeight D K hQuant w B y) ≤
      (PT.π (D.G.patchOf w)).w y := by
  let i := D.G.cellPatch (D.G.cellOf w)
  have hpi : (PT.π (D.G.patchOf w)).w y = (PT.π i).w y := by
    dsimp [i]
    rw [D.G.cellOf_patch]
  have hcard : Fintype.card (Bin PT.tiling (D.G.patchOf w)) =
      Fintype.card (Bin PT.tiling i) :=
    congrArg (fun j => Fintype.card (Bin PT.tiling j)) (D.G.cellOf_patch w).symm
  have hraw := uniform_bin_restores_label D.tiling_valid i hB y
  rw [hpi]
  calc
    _ ≤ (FinLaw.uniform Finset.univ hB).E (fun B =>
        (Fintype.card (Bin PT.tiling i) : ℝ) * (PT.π i).w y *
          if y ∈ B.1 then 1 else 0) := by
      apply Finset.sum_le_sum
      intro B hmem
      apply mul_le_mul_of_nonneg_left _ ((FinLaw.uniform _ _).nonneg B)
      unfold binLabelWeight
      rw [hpi, hcard]
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Nat.cast_nonneg _) ((PT.π i).nonneg y))
      split_ifs <;> simp_all
    _ = _ := hraw

/-- The actual pool moment reduces to a slot-index average, retaining its indicator. -/
theorem moment_le_slot_average {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (μ : FinLaw D.PoolAssignment)
    (hodd : ∀ w ∈ D.externalEarly v, ¬ IsEvenRole w)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w)) (m : ℕ) :
    μ.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ m else 0) ≤
      (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ ((D.externalEarly v).card * m) *
        (FinLaw.pi fun _ : Fin m => trialSlotLaw D v hL).E (fun slots =>
          μ.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
            ∏ i, slotTrialCost D K hQuant v pools (slots i) else 0)) := by
  classical
  let Q := FinLaw.pi fun _ : Fin m => trialSlotLaw D v hL
  let f := fun (pools : D.PoolAssignment)
      (slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v},
        Fin (D.G.nslot (D.G.cellOf w.1))) => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
    ∏ i, slotTrialCost D K hQuant v pools (slots i) else 0
  let err := (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ ((D.externalEarly v).card * m)
  have hpoint : ∀ pools, (if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ m else 0) ≤ err * Q.E (f pools) := by
    intro pools
    by_cases hg : D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools
    · have h := fresh_pow_le_slot_trials D K hQuant v heven pools hg.1 hodd hL m
      simpa only [f, hg, and_self, ite_true, Q, err] using h
    · simp [f, hg, FinLaw.E]
  have hE : μ.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ m else 0) ≤ μ.E (fun pools => err * Q.E (f pools)) := by
    apply Finset.sum_le_sum
    intro pools hpools
    exact mul_le_mul_of_nonneg_left (hpoint pools) (μ.nonneg pools)
  rw [E_const_mul, E_comm] at hE
  exact hE

/-- Apply the shared-slot integral to the actual permission kernels and retained trial tests. -/
theorem retained_flat_bin_integral_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (hEstimate : StarPinnedEstimate D v)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w))
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (m : ℕ)
    (slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1)))
    (forced : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)))
    (P : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C), FinLaw (Bin PT.tiling (D.G.cellPatch a.1)))
    (hP : ∀ a ∉ forced, P a = FinLaw.uniform Finset.univ (hBins a.1)) :
    let e := fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
      (⟨D.G.cellOf o.2.1, slots o.1 o.2⟩ : Σ C : D.G.Cell, Fin (D.G.nslot C))
    let B := trialPinOccurrences e forced
    (FinLaw.pi P).E (fun z =>
      ∑ ys : Fin m → {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
        (∏ o : Fin m × {w : Pos T k // w ∈ D.externalEarly v},
          binLabelWeight D K hQuant o.2.1 (z (e o)) (ys o.1 o.2)) *
            ∏ i, retainedTrialTest D v (fun j => z ⟨D.G.cellOf v, j⟩) (trialPins B i) (ys i)) ≤
      (11 : ℝ) ^ B.card *
        ∏ i : Fin m, if (trialPins B i).card ≤ ListGateContext.pinBudget κ then
          2 * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) else 1 := by
  classical
  dsimp only
  let e := fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
    (⟨D.G.cellOf o.2.1, slots o.1 o.2⟩ : Σ C : D.G.Cell, Fin (D.G.nslot C))
  let B := trialPinOccurrences e forced
  let f := fun (z : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C), Bin PT.tiling (D.G.cellPatch a.1))
    (i : Fin m) => retainedTrialTest D v (fun j => z ⟨D.G.cellOf v, j⟩) (trialPins B i)
  let δ := fun i : Fin m => if (trialPins B i).card ≤ ListGateContext.pinBudget κ then
    2 * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) else 1
  have hlocal : ∀ z z', (∀ a, a ∉ (Finset.univ \ B).image e → z a = z' a) →
      ∀ i ys, f z i ys = f z' i ys := by
    intro z z' hz i ys
    have hown : (fun j => z ⟨D.G.cellOf v, j⟩) = fun j => z' ⟨D.G.cellOf v, j⟩ := by
      funext j
      apply hz
      intro hmem
      obtain ⟨o, ho, heq⟩ := Finset.mem_image.mp hmem
      have hcell : D.G.cellOf o.2.1 = D.G.cellOf v := congrArg Sigma.fst heq
      exact (hQuant.geometry.star_distinct v heven).1 o.2.1 o.2.2 hcell
    dsimp only [f]
    rw [hown]
  have hAverage : ∀ o ∉ B, ∀ y,
      (P (e o)).E (fun z => binLabelWeight D K hQuant o.2.1 z y) ≤
        (ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf o.2.1))).w y := by
    intro o ho y
    have hforced : e o ∉ forced := by
      have h := ho
      simp only [B, trialPinOccurrences, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at h
      exact h.1
    rw [hP (e o) hforced]
    exact binLabelWeight_average D K hQuant o.2.1 (hBins (D.G.cellOf o.2.1)) y
  have hδ : ∀ i, 0 ≤ δ i := by
    intro i
    dsimp [δ]
    split_ifs
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · norm_num
  change (FinLaw.pi P).E (fun z =>
    ∑ ys : Fin m → {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
      (∏ o : Fin m × {w : Pos T k // w ∈ D.externalEarly v},
        binLabelWeight D K hQuant o.2.1 (z (e o)) (ys o.1 o.2)) *
          ∏ i, f z i (ys i)) ≤ (11 : ℝ) ^ B.card * ∏ i, δ i
  refine shared_slot_integral_bound (I := Fin m)
    (J := {w : Pos T k // w ∈ D.externalEarly v})
    (C := Σ C : D.G.Cell, Fin (D.G.nslot C)) (α := Fin (T.S.N k))
    (Ω := fun a => Bin PT.tiling (D.G.cellPatch a.1)) P
    (fun w : {w : Pos T k // w ∈ D.externalEarly v} =>
      ListGateContext.lawAsFinLaw (PT.π (D.G.patchOf w.1))) e B
    (fun o z y => binLabelWeight D K hQuant o.2.1 z y) f ⟨0, T.S.N_pos k⟩
    11 δ (by norm_num) hδ ?_ ?_ ?_ ?_ hAverage hlocal ?_
  · intro o z y
    exact binLabelWeight_nonneg D K hQuant o.2.1 z y
  · intro o z
    exact binLabelWeight_total D K hQuant o.2.1 z (hL o.2.1 o.2.2)
  · intro z i ys
    exact retainedTrialTest_nonneg D v (fun j => z ⟨D.G.cellOf v, j⟩) (trialPins B i) ys
  · intro o ho o' heq
    exact unique_occurrence_fiber e forced o ho o' heq
  · intro z i fixed
    have ht := retainedTrialTest_pinned_bound D K hQuant v heven hEstimate
      (fun j => z ⟨D.G.cellOf v, j⟩) (trialPins B i) fixed
    have hDirac (y : Fin (T.S.N k)) :
        @FinLaw.dirac (Fin (T.S.N k)) (Fin.fintype (T.S.N k))
          (fun a b => Classical.propDecidable (a = b)) y = FinLaw.dirac y := by
      apply finLaw_ext
      intro x
      by_cases hxy : x = y <;> simp [FinLaw.dirac, hxy]
    dsimp only [f, δ]
    simp only [FinLaw.E, FinLaw.pi]
    simp_rw [hDirac]
    simpa only [FinLaw.E, FinLaw.pi] using ht

/-- Expand all actual fixed-slot trials into one joint label-weight sum. -/
theorem slot_trials_label_sum {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (m : ℕ) (pools : D.PoolAssignment)
    (slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1))) :
    (∏ i, slotTrialCost D K hQuant v pools (slots i)) =
      ∑ ys : Fin m → {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
        (∏ o : Fin m × {w : Pos T k // w ∈ D.externalEarly v},
          externalSlotWeight D K hQuant o.2.1 (pools (D.G.cellOf o.2.1))
            (slots o.1 o.2) (ys o.1 o.2)) *
          ∏ i, (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))).pr (fun s =>
            D.gateBad v (D.F.prior (D.G.cellOf v) s v)
              (D.labelsOfPinnedSample v (T.S.N_pos k) (ys i))) := by
  classical
  simp_rw [slotTrialCost_label_sum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]

/-- Replace the actual good-pool indicator by the separate retained trial assertions. -/
theorem slot_trials_retained_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (m : ℕ) (pools : D.PoolAssignment)
    (slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1)))
    (B : Finset (Fin m × {w : Pos T k // w ∈ D.externalEarly v})) :
    (if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
        ∏ i, slotTrialCost D K hQuant v pools (slots i) else 0) ≤
      ∑ ys : Fin m → {w : Pos T k // w ∈ D.externalEarly v} → Fin (T.S.N k),
        (∏ o : Fin m × {w : Pos T k // w ∈ D.externalEarly v},
          externalSlotWeight D K hQuant o.2.1 (pools (D.G.cellOf o.2.1))
            (slots o.1 o.2) (ys o.1 o.2)) *
              ∏ i, retainedTrialTest D v (pools (D.G.cellOf v)) (trialPins B i) (ys i) := by
  classical
  by_cases hg : D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools
  · rw [if_pos hg, slot_trials_label_sum]
    apply Finset.sum_le_sum
    intro ys hys
    have h := compatible_weighted_trials_retained D K hQuant v m pools slots B ys
    rwa [if_pos hg, one_mul] at h
  · rw [if_neg hg]
    apply Finset.sum_nonneg
    intro ys hys
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun o _ => externalSlotWeight_nonneg D K hQuant _ _ _ _)
    · exact Finset.prod_nonneg (fun i _ => retainedTrialTest_nonneg D v _ _ _)

/-- Injecting uniformly chosen slot indices into the complete slot type preserves the atom cap. -/
theorem uniform_slot_map_atom {A : Type*} [Fintype A] [DecidableEq A]
    (L : ℕ) (hL : 0 < L) (e : Fin L → A) (he : Function.Injective e) (a : A) :
    (FinLaw.map (FinLaw.uniform Finset.univ ⟨⟨0, hL⟩, Finset.mem_univ _⟩) e).w a ≤
      1 / (L : ℝ) := by
  classical
  by_cases h : ∃ j, e j = a
  · obtain ⟨j, hj⟩ := h
    dsimp only [FinLaw.map]
    rw [Finset.sum_eq_single j]
    · simp [hj, FinLaw.uniform]
    · intro i hi hij
      have hne : e i ≠ a := fun hi => hij (he (hi.trans hj.symm))
      simp [hne]
    · simp
  · have hnone : ∀ j, e j ≠ a := by simpa using h
    dsimp only [FinLaw.map]
    simp [hnone]

/-- The actual slot lower bound supplies the tenth-power cap used by the rank moment. -/
theorem actual_slots_tenth_power {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (hn : 1 ≤ (T.S.n k : ℝ)) (C : D.G.Cell) :
    (T.S.n k : ℝ) ^ 10 ≤ (D.G.nslot C : ℝ) := by
  have hLow := hQuant.geometry.slots_lower C
  rw [hκ.Ac_eq] at hLow
  norm_num only [Nat.cast_ofNat] at hLow
  have he : (200 : ℝ) - 1 = ((199 : ℕ) : ℝ) := by norm_num
  have hpow : Real.rpow (T.S.n k : ℝ) (199 : ℝ) = (T.S.n k : ℝ) ^ 199 :=
    Real.rpow_natCast (T.S.n k : ℝ) 199
  rw [hpow] at hLow
  exact (pow_le_pow_right₀ hn (by norm_num : 10 ≤ 199)).trans hLow

/-- Flatten independent trial/incidence slot selections even when slot types vary by incidence. -/
theorem pi_E_curry_dependent {C : Type*} [Fintype C] [DecidableEq C]
    {J : C → Type*} [∀ c, Fintype (J c)] [∀ c, DecidableEq (J c)]
    {Ω : ∀ c, J c → Type*} [∀ c j, Fintype (Ω c j)]
    (P : ∀ c j, FinLaw (Ω c j)) (f : (∀ c j, Ω c j) → ℝ) :
    (FinLaw.pi fun c => FinLaw.pi (P c)).E f =
      (FinLaw.pi fun a : Σ c, J c => P a.1 a.2).E
        (fun z => f (fun c j => z ⟨c, j⟩)) := by
  classical
  let e := Equiv.piCurry Ω
  unfold FinLaw.E
  rw [Fintype.sum_equiv e.symm _
    (fun z => (FinLaw.pi fun c => FinLaw.pi (P c)).w (e z) * f (e z))
    (fun s => by simp)]
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  change (∏ c, ∏ j, (P c j).w (z ⟨c, j⟩)) = ∏ a : Σ c, J c, (P a.1 a.2).w (z a)
  exact (Fintype.prod_sigma (fun a : Σ c, J c => (P a.1 a.2).w (z a))).symm


/-- Only trials exceeding the pin budget lose their sparse tail factor. -/
theorem trial_tail_product {I : Type*} [Fintype I] [DecidableEq I]
    (pins : I → ℕ) (s0 : ℕ) (δ : ℝ) :
    (∏ i, if pins i ≤ s0 then δ else 1) =
      δ ^ (Fintype.card I - (Finset.univ.filter fun i => s0 < pins i).card) := by
  classical
  let S := Finset.univ.filter fun i => pins i ≤ s0
  have hprod : (∏ i, if pins i ≤ s0 then δ else 1) = ∏ i ∈ S, δ := by
    rw [← Finset.prod_filter]
  rw [hprod, Finset.prod_const]
  congr 1
  have hpartition := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I))
    (p := fun i => pins i ≤ s0)
  simp only [not_le, Finset.card_univ] at hpartition
  dsimp [S]
  omega

/-- All trial-pin weights and omitted tails are charged to occurrence rank. -/
theorem retained_trials_rank_budget {I J A : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [DecidableEq A]
    (κ : CConsts) (n : ℝ) (hn : 1 ≤ n) (e : I × J → A) (forced : Finset A) :
    (11 : ℝ) ^ (trialPinOccurrences e forced).card *
      (∏ i, if (trialPins (trialPinOccurrences e forced) i).card ≤ ListGateContext.pinBudget κ
        then 2 / n ^ (2 * κ.R) else 1) ≤
      (2 / n ^ (2 * κ.R)) ^ Fintype.card I *
        (121 * n) ^ (Fintype.card (I × J) - ((Finset.univ.image e) \ forced).card) := by
  classical
  rw [trial_tail_product]
  apply trial_rank_budget n hn
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  · exact nonunique_occurrences_le_two_rank e forced
  · exact trialPins_loss_le_rank e forced κ.R _ _ (pinBudget_rank_room κ) rfl

/-- Integrating actual bin images at fixed selections leaves only collision rank. -/
theorem fixed_slots_rank_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (v : Pos T k)
    (heven : IsEvenRole v) (hEstimate : StarPinnedEstimate D v)
    (hn : 1 ≤ (T.S.n k : ℝ))
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w))
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (m : ℕ)
    (slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v}, Fin (D.G.nslot (D.G.cellOf w.1)))
    (forced : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)))
    (P : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C), FinLaw (Bin PT.tiling (D.G.cellPatch a.1)))
    (hP : ∀ a ∉ forced, P a = FinLaw.uniform Finset.univ (hBins a.1)) :
    let e := fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
      (⟨D.G.cellOf o.2.1, slots o.1 o.2⟩ : Σ C : D.G.Cell, Fin (D.G.nslot C))
    (FinLaw.pi P).E (fun z =>
      if D.LocalPoolsTypical v (fun C j => z ⟨C, j⟩) ∧ D.compatiblePool v (fun C j => z ⟨C, j⟩) then
        ∏ i, slotTrialCost D K hQuant v (fun C j => z ⟨C, j⟩) (slots i) else 0) ≤
      (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m *
        (121 * (T.S.n k : ℝ)) ^
          (Fintype.card (Fin m × {w : Pos T k // w ∈ D.externalEarly v}) -
            ((Finset.univ.image e) \ forced).card) := by
  classical
  dsimp only
  let e := fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
    (⟨D.G.cellOf o.2.1, slots o.1 o.2⟩ : Σ C : D.G.Cell, Fin (D.G.nslot C))
  let B := trialPinOccurrences e forced
  have h := retained_flat_bin_integral_bound D K hQuant v heven hEstimate hL hBins m slots forced P hP
  have ht : Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) =
      1 / (T.S.n k : ℝ) ^ (2 * κ.R) := by
    have hcast : (2 : ℝ) * (κ.R : ℝ) = ((2 * κ.R : ℕ) : ℝ) := by simp
    rw [Real.rpow_eq_pow, Real.rpow_neg (by positivity), hcast, Real.rpow_natCast, one_div]
  rw [ht] at h
  have hb := retained_trials_rank_budget κ (T.S.n k : ℝ) hn e forced
  simp only [Fintype.card_fin] at hb
  refine le_trans ?_ (h.trans ?_)
  · apply Finset.sum_le_sum
    intro z hz
    apply mul_le_mul_of_nonneg_left _ ((FinLaw.pi P).nonneg z)
    exact slot_trials_retained_bound D K hQuant v m (fun C j => z ⟨C, j⟩) slots B
  · simpa only [mul_one_div] using hb

/-- Any finite family of independent readouts obeys the same collision-rank moment. -/
theorem readout_collision_moment {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [instA : DecidableEq A] {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (n : ℝ) (hn : 10 ≤ n) (hq : (Fintype.card I : ℝ) ≤ n ^ 2)
    (P : ∀ i, FinLaw (Ω i)) (read : ∀ i, Ω i → A)
    (forced : Finset A) (hforced : forced.card ≤ 1)
    (hcap : ∀ i a, (FinLaw.map (P i) (read i)).w a ≤ 1 / n ^ 10) :
    (FinLaw.pi P).E (fun z => (121 * n) ^
      (Fintype.card I - ((Finset.univ.image (fun i => read i (z i))) \ forced).card)) ≤ 2 := by
  classical
  have hdec : instA = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  rw [hdec] at hcap
  let e := (Fintype.equivFin I).symm
  let f := fun ys : Fin (Fintype.card I) → A =>
    (121 * n) ^ repeatRank (Fintype.card I) forced ys
  have hEq : (FinLaw.pi P).E (fun z => (121 * n) ^
      (Fintype.card I - ((Finset.univ.image (fun i => read i (z i))) \ forced).card)) =
      (FinLaw.pi P).E (fun z => f (fun i => read (e i) (z (e i)))) := by
    congr 1
    funext z
    have hi : Finset.univ.image (fun i => read (e i) (z (e i))) =
        Finset.univ.image (fun i => read i (z i)) := by
      ext a
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi⟩; exact ⟨e i, hi⟩
      · rintro ⟨i, hi⟩; obtain ⟨j, rfl⟩ := e.surjective i; exact ⟨j, hi⟩
    have hr := repeatRank_add_distinct (Fintype.card I) forced (fun i => read (e i) (z (e i)))
    rw [hi] at hr
    dsimp [f]
    congr 1
    omega
  rw [hEq, pi_E_injective_readouts P e e.injective (fun i => read (e i)) f]
  let Q : Fin (Fintype.card I) → FinLaw A := fun i =>
    @FinLaw.map (Ω (e i)) A _ _ (fun a b => Classical.propDecidable (a = b))
      (P (e i)) (read (e i))
  have hbound := collision_rank_moment_two n hn (Fintype.card I) hq Q forced hforced
    (fun i a => hcap (e i) a)
  unfold FinLaw.E FinLaw.pi at hbound ⊢
  convert hbound using 1 <;> congr 1 <;> ext z <;> simp



/-- Actual independent slot selections have bounded collision cost, including one global pin. -/
theorem actual_slot_collision_moment {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (v : Pos T k) (hn : 10 ≤ (T.S.n k : ℝ))
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w))
    (m : ℕ) (hm : (m : ℝ) ≤ (T.S.n k : ℝ))
    (forced : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C))) (hforced : forced.card ≤ 1) :
    (FinLaw.pi fun _ : Fin m => trialSlotLaw D v hL).E (fun slots =>
      (121 * (T.S.n k : ℝ)) ^
        (Fintype.card (Fin m × {w : Pos T k // w ∈ D.externalEarly v}) -
          ((Finset.univ.image (fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
            (⟨D.G.cellOf o.2.1, slots o.1 o.2⟩ : Σ C : D.G.Cell, Fin (D.G.nslot C)))) \ forced).card)) ≤ 2 := by
  classical
  let J := {w : Pos T k // w ∈ D.externalEarly v}
  let I := Σ _i : Fin m, J
  let A := Σ C : D.G.Cell, Fin (D.G.nslot C)
  let P := fun o : I => FinLaw.uniform (Finset.univ : Finset (Fin (D.G.nslot (D.G.cellOf o.2.1))))
    ⟨⟨0, hL o.2.1 o.2.2⟩, Finset.mem_univ _⟩
  let read := fun (o : I) (j : Fin (D.G.nslot (D.G.cellOf o.2.1))) =>
    (⟨D.G.cellOf o.2.1, j⟩ : A)
  have hn1 : 1 ≤ (T.S.n k : ℝ) := by linarith
  have hq : (Fintype.card I : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
    have hd : ((D.externalEarly v).card : ℝ) ≤ (T.S.n k : ℝ) :=
      Nat.cast_le.mpr (Lane_q_s17_pool.externalEarly_card_le D v)
    have hc : Fintype.card I = m * (D.externalEarly v).card := by simp [I, J]
    rw [hc, Nat.cast_mul, pow_two]
    exact mul_le_mul hm hd (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcap : ∀ o a, (FinLaw.map (P o) (read o)).w a ≤ 1 / (T.S.n k : ℝ) ^ 10 := by
    intro o a
    have hinj : Function.Injective (read o) := by
      intro j j' h
      exact eq_of_heq (Sigma.mk.inj h).2
    have h := uniform_slot_map_atom (D.G.nslot (D.G.cellOf o.2.1))
      (hL o.2.1 o.2.2) (read o) hinj a
    refine h.trans ?_
    exact one_div_le_one_div_of_le (by positivity)
      (actual_slots_tenth_power D K hQuant hκ hn1 (D.G.cellOf o.2.1))
  have h := readout_collision_moment (T.S.n k : ℝ) hn hq P read forced hforced hcap
  unfold trialSlotLaw
  rw [pi_E_curry_dependent]
  convert h using 1
  congr 1
  funext z
  have himage : Finset.univ.image
      (fun o : Fin m × J => (⟨D.G.cellOf o.2.1, z ⟨o.1, o.2⟩⟩ : A)) =
      Finset.univ.image (fun o : I => read o (z o)) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, w⟩, hi⟩; exact ⟨⟨i, w⟩, hi⟩
    · rintro ⟨⟨i, w⟩, hi⟩; exact ⟨(i, w), hi⟩
  rw [himage]
  congr 2
  simp [I, J]

/-- A raw or one-pin iid pool law has a flattened product representation. -/
theorem iid_pool_representation {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (hpools : (permPools D.G).Nonempty)
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (ν : FinLaw D.PoolAssignment)
    (hν : ν = iidPoolLaw D.G hpools ∨ ∃ (pin : D.PoolPin)
      (hp : 0 < ∑ pools ∈ D.poolPinSet pin, (iidPoolLaw D.G hpools).w pools),
      ν = FinLaw.cond (iidPoolLaw D.G hpools) (D.poolPinSet pin) hp) :
    ∃ (forced : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)))
      (P : ∀ a : Σ C : D.G.Cell, Fin (D.G.nslot C), FinLaw (Bin PT.tiling (D.G.cellPatch a.1))),
      forced.card ≤ 1 ∧
      (∀ a ∉ forced, P a = FinLaw.uniform Finset.univ (hBins a.1)) ∧
      ∀ f : D.PoolAssignment → ℝ,
        ν.E f = (FinLaw.pi P).E (fun z => f (fun C j => z ⟨C, j⟩)) := by
  classical
  rcases hν with rfl | ⟨pin, hp, rfl⟩
  · refine ⟨∅, fun a => FinLaw.uniform Finset.univ (hBins a.1), by simp, ?_, ?_⟩
    · intro a ha; rfl
    · exact iid_pool_flat_E D hpools hBins
  · refine ⟨{⟨pin.cell, pin.slot⟩}, fun a =>
      if ha : a = ⟨pin.cell, pin.slot⟩ then
        (ha.symm ▸ FinLaw.dirac pin.bin : FinLaw (Bin PT.tiling (D.G.cellPatch a.1)))
      else FinLaw.uniform Finset.univ (hBins a.1), by simp, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_singleton] at ha
      simp only [ha, dite_false]
    · exact iid_pool_pin_flat_E D hpools hBins pin hp

/-- Average the actual raw or one-pin iid experiment over its collision ranks. -/
theorem iid_trial_moment_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (v : Pos T k) (heven : IsEvenRole v) (hEstimate : StarPinnedEstimate D v)
    (hn : 10 ≤ (T.S.n k : ℝ))
    (hodd : ∀ w ∈ D.externalEarly v, ¬ IsEvenRole w)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w))
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (ν : FinLaw D.PoolAssignment)
    (hν : ν = iidPoolLaw D.G hQuant.pool_support_nonempty ∨ ∃ (pin : D.PoolPin)
      (hp : 0 < ∑ pools ∈ D.poolPinSet pin, (iidPoolLaw D.G hQuant.pool_support_nonempty).w pools),
      ν = FinLaw.cond (iidPoolLaw D.G hQuant.pool_support_nonempty) (D.poolPinSet pin) hp)
    (m : ℕ) (hm : (m : ℝ) ≤ (T.S.n k : ℝ)) :
    ν.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ m else 0) ≤
      2 * (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ ((D.externalEarly v).card * m) *
        (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m := by
  classical
  obtain ⟨forced, P, hforced, hP, hRep⟩ :=
    iid_pool_representation D hQuant.pool_support_nonempty hBins ν hν
  have hn1 : 1 ≤ (T.S.n k : ℝ) := by linarith
  let Q := FinLaw.pi fun _ : Fin m => trialSlotLaw D v hL
  let rank := fun slots : Fin m → ∀ w : {w : Pos T k // w ∈ D.externalEarly v},
      Fin (D.G.nslot (D.G.cellOf w.1)) =>
    Fintype.card (Fin m × {w : Pos T k // w ∈ D.externalEarly v}) -
      ((Finset.univ.image (fun o : Fin m × {w : Pos T k // w ∈ D.externalEarly v} =>
        (⟨D.G.cellOf o.2.1, slots o.1 o.2⟩ : Σ C : D.G.Cell, Fin (D.G.nslot C)))) \ forced).card
  have hfixed : ∀ slots, ν.E (fun pools =>
      if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
        ∏ i, slotTrialCost D K hQuant v pools (slots i) else 0) ≤
      (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m * (121 * (T.S.n k : ℝ)) ^ rank slots := by
    intro slots
    rw [hRep]
    exact fixed_slots_rank_bound D K hQuant v heven hEstimate hn1 hL hBins m slots forced P hP
  have havg : Q.E (fun slots => ν.E (fun pools =>
      if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
        ∏ i, slotTrialCost D K hQuant v pools (slots i) else 0)) ≤
      (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m * 2 := by
    calc
      _ ≤ Q.E (fun slots =>
        (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m * (121 * (T.S.n k : ℝ)) ^ rank slots) := by
          apply Finset.sum_le_sum
          intro slots hs
          exact mul_le_mul_of_nonneg_left (hfixed slots) (Q.nonneg slots)
      _ = (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m * Q.E (fun slots =>
          (121 * (T.S.n k : ℝ)) ^ rank slots) := E_const_mul _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (actual_slot_collision_moment D K hQuant hκ v hn hL m hm forced hforced) (by positivity)
  refine (moment_le_slot_average D K hQuant v heven ν hodd hL m).trans ?_
  calc
    _ ≤ (1 + Real.rpow (T.S.n k : ℝ) (-3 : ℝ)) ^ ((D.externalEarly v).card * m) *
        ((2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m * 2) :=
      mul_le_mul_of_nonneg_left havg
        (pow_nonneg (add_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _)
    _ = _ := by ring


/-- The stronger sparse-trial tail absorbs comparison errors in the permutation experiment. -/
theorem perm_trial_moment_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K) (hκ : κ.Admissible)
    (v : Pos T k) (heven : IsEvenRole v) (hEstimate : StarPinnedEstimate D v)
    (hn : 10 ≤ (T.S.n k : ℝ)) (hR : 1 ≤ κ.R)
    (hodd : ∀ w ∈ D.externalEarly v, ¬ IsEvenRole w)
    (hL : ∀ w ∈ D.externalEarly v, 0 < D.G.nslot (D.G.cellOf w))
    (hBins : ∀ C, (Finset.univ : Finset (Bin PT.tiling (D.G.cellPatch C))).Nonempty)
    (μ : FinLaw D.PoolAssignment)
    (hμ : D.IsPermOrPinnedPoolLaw hQuant.pool_support_nonempty μ)
    (m : ℕ) (hm1 : 1 ≤ m) (hm : (m : ℝ) ≤ (T.S.n k : ℝ)) :
    μ.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ m else 0) ≤
      2 * Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * (m : ℝ))) := by
  have hnNat : 2 ≤ T.S.n k := by exact_mod_cast (show (2 : ℝ) ≤ T.S.n k by linarith)
  obtain ⟨ν, hν, hcompare⟩ := trial_moment_iid_reduction D K hQuant v heven hnNat μ hμ m
  have hiid := iid_trial_moment_bound D K hQuant hκ v heven hEstimate hn hodd hL hBins ν hν m hm
  have hn0 : 0 < (T.S.n k : ℝ) := by linarith
  have hthree : Real.rpow (T.S.n k : ℝ) (-3 : ℝ) = 1 / (T.S.n k : ℝ) ^ 3 := by
    rw [Real.rpow_eq_pow, Real.rpow_neg hn0.le, Real.rpow_ofNat, one_div]
  have htail : Real.rpow (T.S.n k : ℝ) (-((κ.R : ℝ) * (m : ℝ))) =
      1 / (T.S.n k : ℝ) ^ (κ.R * m) := by
    rw [Real.rpow_eq_pow, ← Nat.cast_mul, Real.rpow_neg hn0.le, Real.rpow_natCast, one_div]
  rw [hthree] at hcompare hiid
  rw [htail]
  have hbudget := comparison_tail_budget (T.S.n k : ℝ) (by linarith) κ.R
    (D.externalEarly v).card m hR hm1
    (Nat.cast_le.mpr (Lane_q_s17_pool.externalEarly_card_le D v)) hm
  calc
    _ ≤ (1 + 1 / (T.S.n k : ℝ) ^ 3) *
        (2 * (1 + 1 / (T.S.n k : ℝ) ^ 3) ^ ((D.externalEarly v).card * m) *
          (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m) :=
      hcompare.trans (mul_le_mul_of_nonneg_left hiid (by positivity))
    _ = 2 * ((1 + 1 / (T.S.n k : ℝ) ^ 3) ^ ((D.externalEarly v).card * m + 1) *
          (2 / (T.S.n k : ℝ) ^ (2 * κ.R)) ^ m) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by norm_num)

end HypercubeRamsey.Lane_sol_s17_moment
