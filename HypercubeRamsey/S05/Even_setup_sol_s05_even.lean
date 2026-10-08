import HypercubeRamsey.S05.Even_test_sol_s05_even

namespace HypercubeRamsey.Lane_sol_s05_even

open Classical OAI.HypercubeRamsey
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

def refIndices (K : X.Ty) (M : Finset (Fin X.blockBound)) : Finset (Fin (X.p.typeBlocks n K)) :=
  Finset.univ.filter fun i => ∃ j ∈ M, X.blockIdx K j = some i

def replaceArrays {Id : Type} [DecidableEq Id] (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound))
    (z : ∀ _i : refIndices X c.2.1 c.2.2, X.Block c.2.1) : X.ArraysOn Id :=
  Function.update a (c.1, c.2.1) (resampleCoords (refIndices X c.2.1 c.2.2) (a (c.1, c.2.1)) z)

theorem replaceArrays_eq_of_ne {Id : Type} [DecidableEq Id] (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (d : Id × X.Ty) (hd : d ≠ (c.1, c.2.1)) : replaceArrays X a c z d = a d := by
  exact Function.update_of_ne hd _ _

theorem replaceArrays_eq_outside_ref {Id : Type} [DecidableEq Id] (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (z) (d : Id × X.Ty)
    (i : Fin (X.p.typeBlocks n d.2)) (hi : ¬ X.InRef (some c) d i) :
    replaceArrays X a c z d i = a d i := by
  by_cases hd : d = (c.1, c.2.1)
  · subst d
    have hnot : i ∉ refIndices X c.2.1 c.2.2 := by
      intro h
      apply hi
      exact ⟨c, rfl, rfl, (Finset.mem_filter.mp h).2⟩
    simp [replaceArrays, resampleCoords, hnot]
  · rw [replaceArrays_eq_of_ne X a c z d hd]

theorem obsLik_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.obsLikOn H r (replaceArrays X a c z) θ (some c) = X.obsLikOn H r a θ (some c) := by
  unfold Setup5.obsLikOn
  apply Finset.prod_congr rfl
  intro d hd
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : X.InRef (some c) d i
  · simp only [if_pos hi]
  · rw [if_neg hi, if_neg hi, replaceArrays_eq_outside_ref X a c z d i hi]

theorem candGate_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.candGateOn H r (replaceArrays X a c z) θ ↔ X.candGateOn H r a θ := by
  have hhit (d : Id × X.Ty) (M : Finset (Fin X.blockBound)) (hd : r.2.2.2 = some (d.1, d.2, M)) (y : Fin N) :
      X.hitSet (replaceArrays X a c z) d y = X.hitSet a d y := by
    unfold Setup5.hitSet
    rw [replaceArrays_eq_of_ne X a c z d (hmask d M hd)]
  unfold Setup5.candGateOn
  constructor
  · rintro ⟨hden, hm⟩
    refine ⟨hden, ?_⟩
    intro d M hd h
    simpa only [hhit d M hd] using hm d M hd h
  · rintro ⟨hden, hm⟩
    refine ⟨hden, ?_⟩
    intro d M hd h
    simpa only [hhit d M hd] using hm d M hd h

theorem step3Mass_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1)) :
    X.step3MassOn H r (replaceArrays X a c z) (some c) = X.step3MassOn H r a (some c) := by
  unfold Setup5.step3MassOn
  apply Finset.sum_congr rfl
  intro θ _
  rw [propext (candGate_delete_replace X H r a c z hmask θ), obsLik_delete_replace X H r a c z θ]

theorem step3Post_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn H r (replaceArrays X a c z) (some c) θ = X.step3PostOn H r a (some c) θ := by
  unfold Setup5.step3PostOn
  rw [propext (candGate_delete_replace X H r a c z hmask θ), obsLik_delete_replace X H r a c z θ,
    step3Mass_delete_replace X H r a c z hmask]

theorem highDeleted_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1))
    (h : Fin (colLen5 (X.p.s n) r.1)) :
    X.highDeleted H r (replaceArrays X a c z) c h = X.highDeleted H r a c h := by
  unfold Setup5.highDeleted
  have hpost : X.step3PostOn H r (replaceArrays X a c z) (some c) = X.step3PostOn H r a (some c) :=
    funext (step3Post_delete_replace X H r a c z hmask)
  rw [hpost]

theorem step3Post_ignore_designations {Id : Type} (H : X.KeyHist) (r r' : X.RecordOn Id)
    (a : X.ArraysOn Id) (c : Option (Id × X.Ty × Finset (Fin X.blockBound)))
    (htarget : r.1 = r'.1) (hobs : r.2.1 = r'.2.1) (hmask : r.2.2.2 = r'.2.2.2)
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) :
    X.step3PostOn H r a c θ = X.step3PostOn H r' a c (htarget ▸ θ) := by
  rcases r with ⟨k, obs, refs, mask⟩
  rcases r' with ⟨k', obs', refs', mask'⟩
  dsimp only at htarget hobs hmask
  subst k'
  subst obs'
  subst mask'
  rfl

theorem step3Post_nonneg {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Option (Id × X.Ty × Finset (Fin X.blockBound)))
    (θ : Fin (colLen5 (X.p.s n) r.1) → Fin N) : 0 ≤ X.step3PostOn H r a c θ := by
  unfold Setup5.step3PostOn
  apply div_nonneg
  · apply mul_nonneg
    · exact mul_nonneg (Finset.prod_nonneg fun h _ => (X.prior H.1 r.1).nonneg (θ h))
        (by split_ifs <;> norm_num)
    · exact Lane_sol_s05_hist1b.obsLikOn_nonneg X H r a θ c
  · exact Lane_sol_s05_hist1b.step3MassOn_nonneg X H r a c

theorem step3Post_sum_le_one {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Option (Id × X.Ty × Finset (Fin X.blockBound))) :
    ∑ θ, X.step3PostOn H r a c θ ≤ 1 := by
  unfold Setup5.step3PostOn
  rw [← Finset.sum_div]
  change X.step3MassOn H r a c / X.step3MassOn H r a c ≤ 1
  by_cases hz : X.step3MassOn H r a c = 0
  · simp [hz]
  · rw [div_self hz]

theorem lowPost_sum_le_one {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Option (Id × X.Ty × Finset (Fin X.blockBound))) (hl : r.1.isLeft) :
    ∑ y, X.step3PostOn H r a c (fun _ => y) ≤ 1 := by
  have hlen : colLen5 (X.p.s n) r.1 = 1 := by
    cases hk : r.1 with
    | inl k => simp [colLen5, hk]
    | inr k => simp [hk] at hl
  let i₀ : Fin (colLen5 (X.p.s n) r.1) := ⟨0, by omega⟩
  let f : Fin N → (Fin (colLen5 (X.p.s n) r.1) → Fin N) := fun y _ => y
  have hf : Function.Injective f := by
    intro y y' heq
    exact congrFun heq i₀
  calc
    _ = ∑ θ ∈ Finset.univ.image f, X.step3PostOn H r a c θ := by
      rw [Finset.sum_image]
      intro y hy y' hy' heq
      exact hf heq
    _ ≤ ∑ θ, X.step3PostOn H r a c θ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun θ _ _ => step3Post_nonneg X H r a c θ)
    _ ≤ 1 := step3Post_sum_le_one X H r a c

theorem normalize5_dominates {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℝ) (ω₀ : Ω) (hf : ∀ ω, 0 ≤ f ω) (hs : ∑ ω, f ω ≤ 1) (ω : Ω) :
    f ω ≤ (normalize5 f ω₀).w ω := by
  by_cases hpos : 0 < ∑ ω, f ω
  · rw [Lane_q_s05_hist1b.normalize5_weight_eq_div_of_nonneg f ω₀ ω hf hpos]
    apply (le_div_iff₀ hpos).mpr
    simpa using mul_le_mul_of_nonneg_left hs (hf ω)
  · have hs0 : ∑ ω, f ω = 0 := le_antisymm (le_of_not_gt hpos) (Finset.sum_nonneg fun ω _ => hf ω)
    have hw : f ω = 0 := by
      have hh := Finset.single_le_sum (fun ω _ => hf ω) (Finset.mem_univ ω)
      rw [hs0] at hh
      exact le_antisymm hh (hf ω)
    rw [hw]
    exact (normalize5 f ω₀).nonneg ω

def lowDeletedLaw {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) : Law N :=
  normalize5 (fun y => X.step3PostOn H r a (some c) (fun _ => y)) X.y₀

theorem lowDeletedLaw_dominates {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hl : r.1.isLeft) (y : Fin N) :
    X.step3PostOn H r a (some c) (fun _ => y) ≤ (lowDeletedLaw X H r a c).w y :=
  normalize5_dominates _ _ (fun y => step3Post_nonneg X H r a (some c) _) (lowPost_sum_le_one X H r a _ hl) y

theorem lowDeletedLaw_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1)) :
    lowDeletedLaw X H r (replaceArrays X a c z) c = lowDeletedLaw X H r a c := by
  unfold lowDeletedLaw
  congr 1
  funext y
  exact step3Post_delete_replace X H r a c z hmask _

def uniformMixture {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (S : Finset I) (hS : S.Nonempty) (Q : I → FinProb O) : FinProb O :=
  FinProb.map (FinProb.bind (FinProb.uniform S hS) Q) Prod.snd

theorem uniformMixture_weight {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (S : Finset I) (hS : S.Nonempty) (Q : I → FinProb O) (x : O) :
    (uniformMixture S hS Q).w x = (S.card : ℝ)⁻¹ * ∑ i ∈ S, (Q i).w x := by
  unfold uniformMixture FinProb.map
  change (∑ ix : I × O, if ix.2 = x then (FinProb.uniform S hS).w ix.1 * (Q ix.1).w ix.2 else 0) = _
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change (∑ i, (if i ∈ S then (S.card : ℝ)⁻¹ else 0) * (Q i).w x) = _
  rw [Finset.mul_sum]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun i : I => i ∈ S) = S := by
    ext i
    simp
  rw [hfilter]

theorem uniformMixture_component {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (S : Finset I) (hS : S.Nonempty) (Q : I → FinProb O) (i : I) (hi : i ∈ S) (x : O) :
    (Q i).w x ≤ (S.card : ℝ) * (uniformMixture S hS Q).w x := by
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
  rw [uniformMixture_weight]
  have hh := Finset.single_le_sum (fun j _ => (Q j).nonneg x) hi
  rw [← mul_assoc, mul_inv_cancel₀ hcard.ne', one_mul]
  exact hh

theorem map_injective_weight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinProb A) (f : A → B) (hf : Function.Injective f) (a : A) :
    (FinProb.map P f).w (f a) = P.w a := by
  classical
  change (∑ b, if f b = f a then P.w b else 0) = P.w a
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hne
    simp [hf.ne hne]
  · intro h
    exact (h (Finset.mem_univ a)).elim

theorem colLen_of_right (k : X.Key) (hk : k.isRight) : colLen5 (X.p.s n) k = X.p.s n := by
  cases k with
  | inl k => simp at hk
  | inr k => rfl

def highDeletedOutLaw {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hs : 0 < X.p.s n) (hr : r.1.isRight) : FinProb X.OddOut :=
  FinProb.map (FinProb.bind (FinProb.uniformAll (Ω := Fin (X.p.s n)) ⟨⟨0, hs⟩⟩)
    (fun h => X.highDeleted H r a c (Fin.cast (colLen_of_right X r.1 hr).symm h)))
    (fun hy => (hy.1.castSucc, hy.2))

theorem highDeletedOutLaw_weight {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hs : 0 < X.p.s n) (hr : r.1.isRight)
    (h : Fin (X.p.s n)) (y : Fin N) :
    (highDeletedOutLaw X H r a c hs hr).w (h.castSucc, y) =
      (X.highDeleted H r a c (Fin.cast (colLen_of_right X r.1 hr).symm h)).w y / (X.p.s n : ℝ) := by
  let f : Fin (X.p.s n) × Fin N → X.OddOut := fun hy => (hy.1.castSucc, hy.2)
  have hf : Function.Injective f := by
    intro u v huv
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun o : X.OddOut => o.1.val) huv
    · exact congrArg (fun o : X.OddOut => o.2) huv
  have hh := map_injective_weight
    (FinProb.bind (FinProb.uniformAll (Ω := Fin (X.p.s n)) ⟨⟨0, hs⟩⟩)
      (fun h => X.highDeleted H r a c (Fin.cast (colLen_of_right X r.1 hr).symm h))) f hf (h, y)
  simpa only [highDeletedOutLaw, FinProb.bind, FinProb.uniformAll, Fintype.card_fin, div_eq_mul_inv, mul_comm] using hh

theorem highDeletedOutLaw_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1))
    (hs : 0 < X.p.s n) (hr : r.1.isRight) :
    highDeletedOutLaw X H r (replaceArrays X a c z) c hs hr = highDeletedOutLaw X H r a c hs hr := by
  unfold highDeletedOutLaw
  congr 2
  funext h
  exact highDeleted_delete_replace X H r a c z hmask _

theorem logplus_dom (r q : ℝ) (hr : 0 ≤ r) (hq : 0 < q) :
    r ≤ Real.exp (max 0 (Real.log (r / q))) * q := by
  by_cases hz : r = 0
  · rw [hz]
    positivity
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    have hh := Real.exp_le_exp.mpr (le_max_right (0 : ℝ) (Real.log (r / q)))
    rw [Real.exp_log (div_pos hrpos hq)] at hh
    exact (div_le_iff₀ hq).mp hh

theorem highCost_dominates_row {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound))
    (R : X.OddOut → ℝ) (hR : ∀ o, 0 ≤ R o) (hindex : ∀ o, X.p.s n ≤ o.1.val → R o = 0)
    (hs : 0 < X.p.s n) (hr : r.1.isRight) (o : X.OddOut) :
    R o ≤ Real.exp (X.highCost H r a c R o) * (highDeletedOutLaw X H r a c hs hr).w o := by
  by_cases hi : o.1.val < X.p.s n
  · let h : Fin (X.p.s n) := ⟨o.1.val, hi⟩
    have ho : (h.castSucc, o.2) = o := Prod.ext (Fin.ext rfl) rfl
    have hw := highDeletedOutLaw_weight X H r a c hs hr h o.2
    rw [ho] at hw
    have hidx : X.idxOf r.1 o = some (Fin.cast (colLen_of_right X r.1 hr).symm h) := by
      unfold Setup5.idxOf
      have hlt : o.1.val < colLen5 (X.p.s n) r.1 := by rw [colLen_of_right X r.1 hr]; exact hi
      simp only [dif_pos hlt]
      congr 1
    have hN : 0 < (N : ℝ) := by exact_mod_cast Fin.pos X.y₀
    have hsR : 0 < (X.p.s n : ℝ) := by exact_mod_cast hs
    have hlow := smooth_lower X
      (X.condCoord (X.step3PostOn H r a (some c)) (H.2 r.1) (Fin.cast (colLen_of_right X r.1 hr).symm h)) o.2
    have hq : 0 < (X.highDeleted H r a c (Fin.cast (colLen_of_right X r.1 hr).symm h)).w o.2 /
        (X.p.s n : ℝ) := by
      apply div_pos _ hsR
      exact lt_of_lt_of_le (by positivity) hlow
    rw [Setup5.highCost, hidx, hw]
    exact logplus_dom (R o) _ (hR o) hq
  · rw [hindex o (by omega)]
    exact mul_nonneg (Real.exp_pos _).le ((highDeletedOutLaw X H r a c hs hr).nonneg o)

theorem highDeleted_ignore_refs {Id : Type} (H : X.KeyHist) (k : X.Key)
    (obs : Finset (Id × X.Ty)) (refs refs' : Finset (Id × X.Ty × Option X.Key))
    (mask : Option (Id × X.Ty × Finset (Fin X.blockBound))) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (h : Fin (colLen5 (X.p.s n) k)) :
    X.highDeleted H (k, obs, refs, mask) a c h = X.highDeleted H (k, obs, refs', mask) a c h := rfl

theorem lowDeletedLaw_ignore_refs {Id : Type} (H : X.KeyHist) (k : X.Key)
    (obs : Finset (Id × X.Ty)) (refs refs' : Finset (Id × X.Ty × Option X.Key))
    (mask : Option (Id × X.Ty × Finset (Fin X.blockBound))) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) :
    lowDeletedLaw X H (k, obs, refs, mask) a c = lowDeletedLaw X H (k, obs, refs', mask) a c := rfl

theorem arraysOf_replaceBlockData {h : X.HeightChoice5} (ω : X.CΩ h) (l : h.hp.Loc) (K : X.Ty)
    (M : Finset (Fin X.blockBound)) (z : ∀ _i : refIndices X K M, X.Block K) :
    Setup5.arraysOf (replaceBlockData X ω l K (refIndices X K M) z) =
      replaceArrays X (Setup5.arraysOf ω) (l, K, M) z := by
  funext d
  obtain ⟨l', K'⟩ := d
  by_cases hl : l' = l
  · subst l'
    by_cases hK : K' = K
    · subst K'
      simp [Setup5.arraysOf, Setup5.arr, replaceBlockData, replaceArrays]
    · have hpair : (l, K') ≠ (l, K) := by intro h; exact hK (congrArg Prod.snd h)
      simp [Setup5.arraysOf, Setup5.arr, replaceBlockData, replaceArrays, Function.update_of_ne hK,
        Function.update_of_ne hpair]
  · have hpair : (l', K') ≠ (l, K) := by intro h; exact hl (congrArg Prod.fst h)
    simp [Setup5.arraysOf, Setup5.arr, replaceBlockData, replaceArrays, Function.update_of_ne hl,
      Function.update_of_ne hpair]

def lowDeletedOutLaw {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) : FinProb X.OddOut :=
  FinProb.map (lowDeletedLaw X H r a c) (fun y => (0, y))

theorem lowDeletedOutLaw_weight {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (y : Fin N) :
    (lowDeletedOutLaw X H r a c).w (0, y) = (lowDeletedLaw X H r a c).w y := by
  exact map_injective_weight _ (fun y : Fin N => ((0 : Fin (X.p.s n + 1)), y))
    (fun y y' h => congrArg Prod.snd h) y

theorem lowDeletedOutLaw_delete_replace {Id : Type} [DecidableEq Id] (H : X.KeyHist)
    (r : X.RecordOn Id) (a : X.ArraysOn Id) (c : Id × X.Ty × Finset (Fin X.blockBound)) (z)
    (hmask : ∀ d M, r.2.2.2 = some (d.1, d.2, M) → d ≠ (c.1, c.2.1)) :
    lowDeletedOutLaw X H r (replaceArrays X a c z) c = lowDeletedOutLaw X H r a c := by
  unfold lowDeletedOutLaw
  rw [lowDeletedLaw_delete_replace X H r a c z hmask]

theorem lowDeletion_dominates_row {Id : Type} (H : X.KeyHist) (r : X.RecordOn Id) (a : X.ArraysOn Id)
    (c : Id × X.Ty × Finset (Fin X.blockBound)) (hl : r.1.isLeft)
    (R : X.OddOut → ℝ) (hindex : ∀ o, o.1.val ≠ 0 → R o = 0)
    (hdel : ∀ o, R o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) *
      X.step3PostOn H r a (some c) (fun _ => o.2)) (o : X.OddOut) :
    R o ≤ Real.exp (X.p.a 4 * X.refLen c.2.1 c.2.2) * (lowDeletedOutLaw X H r a c).w o := by
  by_cases hi : o.1.val = 0
  · have ho : (0, o.2) = o := Prod.ext (Fin.ext hi.symm) rfl
    have hw := lowDeletedOutLaw_weight X H r a c o.2
    rw [ho] at hw
    rw [hw]
    exact (hdel o).trans (mul_le_mul_of_nonneg_left (lowDeletedLaw_dominates X H r a c hl o.2) (Real.exp_pos _).le)
  · rw [hindex o hi]
    exact mul_nonneg (Real.exp_pos _).le ((lowDeletedOutLaw X H r a c).nonneg o)

end
end HypercubeRamsey.Lane_sol_s05_even
