import HypercubeRamsey.S05.History_q_s05_hist1b

namespace HypercubeRamsey.Lane_sol_s05_hist1b

open Classical OAI.HypercubeRamsey
open scoped BigOperators

noncomputable section

set_option synthInstance.maxSize 1024

variable {γ K' χ : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
variable (X : Setup5 γ K' χ n N E G)

/-- Replace the sampled prefix, keeping the parents and all other stream data. -/
def putBlock (b : X.Base) (K : X.Ty) (z : X.Block K) : X.Base :=
  (b.1, b.2.1, X.replaceStream b.2.2 K.1.1 z)

theorem replace_replace (W : BinVector5 n → X.Stream) (w : BinVector5 n)
    {k : ℕ} (z z' : Fin k → Word5 N X.p.q0) :
    X.replaceStream (X.replaceStream W w z) w z' = X.replaceStream W w z' := by
  funext v s
  by_cases hv : v = w
  · subst v
    by_cases hs : (s : ℕ) < k <;> simp [Setup5.replaceStream, hs]
  · simp [Setup5.replaceStream, hv]

theorem putBlock_putBlock (b : X.Base) (K : X.Ty) (z z' : X.Block K) :
    putBlock X (putBlock X b K z) K z' = putBlock X b K z' := by
  simp [putBlock, replace_replace]

theorem trueBlock_putBlock (b : X.Base) (K : X.Ty) (z : X.Block K) :
    X.trueBlock (putBlock X b K z) K = z := by
  funext s
  have hs : (s : ℕ) < X.p.streamSegs n :=
    lt_of_lt_of_le s.isLt (Lane_q_s05_hist1b.typeSegs_le_streamSegs X K)
  simp [Setup5.trueBlock, putBlock, Setup5.replaceStream, hs, s.isLt]

theorem putBlock_trueBlock (b : X.Base) (K : X.Ty) :
    putBlock X b K (X.trueBlock b K) = b := by
  have hstream : X.replaceStream b.2.2 K.1.1 (X.trueBlock b K) = b.2.2 := by
    funext w s
    by_cases hw : w = K.1.1
    · subst w
      by_cases hs : (s : ℕ) < X.p.typeSegs n K
      · simp [Setup5.replaceStream, Setup5.trueBlock, hs, s.isLt]
      · simp [Setup5.replaceStream, hs]
    · simp [Setup5.replaceStream, hw]
  simp [putBlock, hstream]

theorem blockBase_putBlock (b : X.Base) (K : X.Ty) (z z' : X.Block K) :
    X.blockBase (putBlock X b K z) K z' = X.blockBase b K z' := rfl

theorem colWeight_deleted_putBlock (b : X.Base) (K : X.Ty) (z : X.Block K)
    (ℓ : X.Key) (y : Fin N) :
    X.colWeight (putBlock X b K z) ℓ (putBlock X b K z).2.2
        (fun w s => ¬ (w = K.1.1 ∧ (s : ℕ) < X.p.typeSegs n K)) y =
      X.colWeight b ℓ b.2.2
        (fun w s => ¬ (w = K.1.1 ∧ (s : ℕ) < X.p.typeSegs n K)) y := by
  simp only [Setup5.colWeight, putBlock]
  split_ifs
  · congr 1
    apply Finset.prod_congr rfl
    intro w _
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    by_cases hw : w = K.1.1 <;> by_cases hs : (s : ℕ) < X.p.typeSegs n K <;>
      simp [Setup5.replaceStream, hw, hs]
  · congr 1
    apply Finset.prod_congr rfl
    intro s _
    by_cases hw : ℓ.coarse.1 = K.1.1 <;> by_cases hs : (s : ℕ) < X.p.typeSegs n K <;>
      simp [Setup5.replaceStream, hw, hs]

theorem priorDel_putBlock (b : X.Base) (K : X.Ty) (z : X.Block K) (ℓ : X.Key) :
    X.priorDel (putBlock X b K z) ℓ K.1.1 (X.p.typeSegs n K) =
      X.priorDel b ℓ K.1.1 (X.p.typeSegs n K) := by
  unfold Setup5.priorDel
  congr 1
  funext y
  exact colWeight_deleted_putBlock X b K z ℓ y

theorem priorRep_putBlock (b : X.Base) (K : X.Ty) (z z' : X.Block K) (ℓ : X.Key) :
    X.priorRep (putBlock X b K z) ℓ K.1.1 z' = X.priorRep b ℓ K.1.1 z' := by
  simp only [Setup5.priorRep, putBlock, replace_replace]
  congr 1

theorem blockGate_putBlock (b : X.Base) (K : X.Ty) (z z' : X.Block K) :
    X.blockGate (putBlock X b K z) K z' ↔ X.blockGate b K z' := by
  simp only [Setup5.blockGate, priorRep_putBlock, priorDel_putBlock]

theorem colLik_putBlock (b : X.Base) (K : X.Ty) (z z' : X.Block K) (ℓ : X.Key)
    (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    X.colLik (putBlock X b K z) K ℓ z' θ = X.colLik b K ℓ z' θ := by
  simp only [Setup5.colLik, priorRep_putBlock, priorDel_putBlock]

theorem blockMass_putBlock (b : X.Base) (U : X.Hidden) (K : X.Ty)
    (z : X.Block K) (keys : Finset X.Key) :
    X.blockMass (putBlock X b K z, U) K keys = X.blockMass (b, U) K keys := by
  simp only [Setup5.blockMass, Setup5.blockWeight, blockBase_putBlock,
    blockGate_putBlock, colLik_putBlock]

private theorem prod_prefix {k t : ℕ} (hkt : k ≤ t) (f : Fin t → ℝ) :
    (∏ s : Fin t, if (s : ℕ) < k then f s else 1) =
      ∏ s : Fin k, f (Fin.castLE hkt s) := by
  let S : Finset (Fin t) := Finset.univ.filter fun s => (s : ℕ) < k
  let e : Fin k ≃ {s : Fin t // s ∈ S} := {
    toFun := fun s => ⟨Fin.castLE hkt s, by simp [S, s.isLt]⟩
    invFun := fun s => ⟨s.1.val, (Finset.mem_filter.mp s.2).2⟩
    left_inv := by intro s; rfl
    right_inv := by intro s; rfl }
  calc
    _ = ∏ s ∈ S, f s := by simp [S, Finset.prod_filter]
    _ = ∏ s : {s : Fin t // s ∈ S}, f s.1 := by
      rw [Finset.univ_eq_attach]
      exact (Finset.prod_attach S f).symm
    _ = ∏ s : Fin k, f (Fin.castLE hkt s) :=
      (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm

private theorem prefix_swap {Ω : Type*} {k t : ℕ} (hkt : k ≤ t)
    (f : Ω → ℝ) (u : Fin t → Ω) (z : Fin k → Ω) :
    (∏ s, f (u s)) * (∏ s, f (z s)) =
      (∏ s : Fin t, f (if h : (s : ℕ) < k then z ⟨s, h⟩ else u s)) *
        (∏ s : Fin k, f (u (Fin.castLE hkt s))) := by
  let v : Fin t → Ω := fun s => if h : (s : ℕ) < k then z ⟨s, h⟩ else u s
  have hsplit (u : Fin t → Ω) : (∏ s, f (u s)) =
      (∏ s : Fin k, f (u (Fin.castLE hkt s))) *
        (∏ s : Fin t, if (s : ℕ) < k then 1 else f (u s)) := by
    rw [← prod_prefix hkt (fun s => f (u s))]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s _
    split_ifs <;> simp
  have hpref : (∏ s : Fin k, f (v (Fin.castLE hkt s))) = ∏ s, f (z s) := by
    apply Finset.prod_congr rfl
    intro s _
    simp [v, s.isLt]
  have htail : (∏ s : Fin t, if (s : ℕ) < k then 1 else f (v s)) =
      ∏ s : Fin t, if (s : ℕ) < k then 1 else f (u s) := by
    apply Finset.prod_congr rfl
    intro s _
    split_ifs with hs <;> simp [v, hs]
  change _ = (∏ s, f (v s)) * _
  rw [hsplit u, hsplit v, hpref, htail]
  ring

theorem base_block_swap (b : X.Base) (K : X.Ty) (z : X.Block K) :
    X.baseLaw.w b * X.blockBase b K z =
      X.baseLaw.w (putBlock X b K z) *
        X.blockBase (putBlock X b K z) K (X.trueBlock b K) := by
  let f : BinVector5 n → ℝ := fun w =>
    ∏ s, (X.segLaw b.1 (b.2.1 w)).w (b.2.2 w s)
  let g : BinVector5 n → ℝ := fun w =>
    ∏ s, (X.segLaw b.1 (b.2.1 w)).w ((putBlock X b K z).2.2 w s)
  have hfg : ∀ w, w ≠ K.1.1 → f w = g w := by
    intro w hw
    simp [f, g, putBlock, Setup5.replaceStream, hw]
  have htarget : f K.1.1 * X.blockBase b K z =
      g K.1.1 * X.blockBase b K (X.trueBlock b K) := by
    have hkt := Lane_q_s05_hist1b.typeSegs_le_streamSegs X K
    have ht : X.trueBlock b K = fun s => b.2.2 K.1.1 (Fin.castLE hkt s) := by
      funext s
      have hs := lt_of_lt_of_le s.isLt hkt
      simp only [Setup5.trueBlock, dif_pos hs]
      rfl
    rw [ht]
    simpa [f, g, putBlock, Setup5.replaceStream, Setup5.blockBase] using prefix_swap hkt
        (fun x => (X.segLaw b.1 (b.2.1 K.1.1)).w x) (b.2.2 K.1.1) z
  have herase : (∏ w ∈ Finset.univ.erase K.1.1, f w) =
      ∏ w ∈ Finset.univ.erase K.1.1, g w := by
    apply Finset.prod_congr rfl
    intro w hw
    exact hfg w (Finset.mem_erase.mp hw).1
  have hprod : (∏ w, f w) * X.blockBase b K z =
      (∏ w, g w) * X.blockBase b K (X.trueBlock b K) := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ K.1.1),
      ← Finset.mul_prod_erase Finset.univ g (Finset.mem_univ K.1.1), herase]
    calc
      _ = (∏ w ∈ Finset.univ.erase K.1.1, g w) *
          (f K.1.1 * X.blockBase b K z) := by ring
      _ = _ := by rw [htarget]; ring
  rw [Lane_q_s05_hist1b.baseLaw_weight_factor5,
    Lane_q_s05_hist1b.baseLaw_weight_factor5, blockBase_putBlock]
  change (X.P.prior.parent.w b.1 *
    (∏ w, (X.P.prior.partner b.1 w).w (b.2.1 w))) * (∏ w, f w) * _ =
    (X.P.prior.parent.w b.1 *
    (∏ w, (X.P.prior.partner b.1 w).w (b.2.1 w))) * (∏ w, g w) * _
  rw [mul_assoc, mul_assoc, hprod]
  ring

theorem blockBase_sum (b : X.Base) (K : X.Ty) : ∑ z, X.blockBase b K z = 1 :=
  (FinProb.pi fun _ : Fin (X.p.typeSegs n K) =>
    X.segLaw b.1 (b.2.1 K.1.1)).sum_eq_one

/-- The raw base law is invariant under a fresh true-parent prefix draw. -/
theorem base_expect_resample (K : X.Ty) (f : X.Base → ℝ) :
    X.baseLaw.expect f = X.baseLaw.expect (fun b =>
      ∑ z, X.blockBase b K z * f (putBlock X b K z)) := by
  let e : X.Base × X.Block K ≃ X.Base × X.Block K := {
    toFun := fun bz => (putBlock X bz.1 K bz.2, X.trueBlock bz.1 K)
    invFun := fun bz => (putBlock X bz.1 K bz.2, X.trueBlock bz.1 K)
    left_inv := by intro bz; simp [putBlock_putBlock, trueBlock_putBlock, putBlock_trueBlock]
    right_inv := by intro bz; simp [putBlock_putBlock, trueBlock_putBlock, putBlock_trueBlock] }
  let F : X.Base × X.Block K → ℝ := fun bz =>
    X.baseLaw.w bz.1 * X.blockBase bz.1 K bz.2 * f bz.1
  have heq : (∑ bz, F (e bz)) = ∑ bz, F bz := Equiv.sum_comp e F
  have hpoint (bz : X.Base × X.Block K) : F (e bz) =
      X.baseLaw.w bz.1 * X.blockBase bz.1 K bz.2 * f (putBlock X bz.1 K bz.2) := by
    dsimp [F, e]
    rw [← base_block_swap]
  simp_rw [hpoint] at heq
  conv at heq => lhs; rw [Fintype.sum_prod_type]
  conv at heq => rhs; rw [Fintype.sum_prod_type]
  simp only [F] at heq
  have hright : (∑ b, ∑ z, X.baseLaw.w b * X.blockBase b K z * f b) =
      X.baseLaw.expect f := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro b _
    calc
      _ = X.baseLaw.w b * f b * (∑ z, X.blockBase b K z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [blockBase_sum]; ring
  rw [hright] at heq
  rw [← heq]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

private theorem prod_subtype {ι : Type*} [Fintype ι] (S : Finset ι) (f : ι → ℝ) :
    (∏ i : {i // i ∈ S}, f i.1) = ∏ i ∈ S, f i := by
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach S f

/-- Integrate the unused coordinates before changing the selected coordinate weights. -/
theorem pi_change_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P Q : ∀ i, FinProb (Ω i)) (S : Finset ι)
    (L : ∀ i, Ω i → ℝ) (f : (∀ i, Ω i) → ℝ) (u₀ : ∀ i, Ω i)
    (hf : FinProb.DependsOn f S)
    (hw : ∀ i ∈ S, ∀ x, (P i).w x = (Q i).w x * L i x) :
    (FinProb.pi P).expect f =
      (FinProb.pi Q).expect (fun u => (∏ i ∈ S, L i (u i)) * f u) := by
  have hdep : FinProb.DependsOn (fun u => (∏ i ∈ S, L i (u i)) * f u) S := by
    intro u v huv
    dsimp only
    rw [hf u v huv]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [huv i hi]
  rw [FinProb.pi_expect_depends P S f u₀ hf,
    FinProb.pi_expect_depends Q S _ u₀ hdep]
  unfold FinProb.expect FinProb.pi
  apply Finset.sum_congr rfl
  intro a _
  let u := (Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) Ω).symm
    (a, fun i => u₀ i.1)
  have hL : (∏ i ∈ S, L i (u i)) = ∏ i : {i // i ∈ S}, L i.1 (a i) := by
    rw [← prod_subtype S]
    apply Finset.prod_congr rfl
    intro i _
    simp only [u, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos i.2]
  change (∏ i : {i // i ∈ S}, (P i.1).w (a i)) * f u =
    (∏ i : {i // i ∈ S}, (Q i.1).w (a i)) * ((∏ i ∈ S, L i (u i)) * f u)
  have hprod : (∏ i : {i // i ∈ S}, (P i.1).w (a i)) =
      (∏ i : {i // i ∈ S}, (Q i.1).w (a i)) *
        (∏ i : {i // i ∈ S}, L i.1 (a i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact hw i.1 i.2 (a i)
  rw [hprod, hL]
  ring

theorem blockMass_hidden_congr (b : X.Base) (U V : X.Hidden) (K : X.Ty)
    (keys : Finset X.Key) (h : ∀ ℓ ∈ keys, U ℓ = V ℓ) :
    X.blockMass (b, U) K keys = X.blockMass (b, V) K keys := by
  unfold Setup5.blockMass Setup5.blockWeight
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  change X.colLik b K ℓ z (U ℓ) = X.colLik b K ℓ z (V ℓ)
  rw [h ℓ hℓ]

def deletedHidden (b : X.Base) (K : X.Ty) : FinProb X.Hidden :=
  FinProb.pi fun ℓ => FinProb.pi fun _ => X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)

theorem deleted_likelihood_integral (b : X.Base) (K : X.Ty)
    (keys : Finset X.Key) (z : X.Block K) :
    (deletedHidden X b K).expect (fun U => ∏ ℓ ∈ keys, X.colLik b K ℓ z (U ℓ)) ≤ 1 := by
  let Q (ℓ : X.Key) := FinProb.pi fun _ : Fin (colLen5 (X.p.s n) ℓ) =>
    X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)
  let L (ℓ : X.Key) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) : ℝ :=
    if ℓ ∈ keys then X.colLik b K ℓ z θ else 1
  have hL : ∀ U : X.Hidden, (∏ ℓ, L ℓ (U ℓ)) = ∏ ℓ ∈ keys, X.colLik b K ℓ z (U ℓ) := by
    intro U
    simp [L, Finset.prod_ite]
  have hsingle (ℓ : X.Key) : (Q ℓ).expect (L ℓ) ≤ 1 := by
    by_cases hℓ : ℓ ∈ keys
    · simpa [Q, L, hℓ, FinProb.expect, FinProb.pi, Setup5.colLik] using
        Lane_q_s05_hist1b.pi_likelihood_weight_sum_le_one5
          (fun _ : Fin (colLen5 (X.p.s n) ℓ) => X.priorRep b ℓ K.1.1 z)
          (fun _ : Fin (colLen5 (X.p.s n) ℓ) => X.priorDel b ℓ K.1.1 (X.p.typeSegs n K))
    · simp [L, hℓ, FinProb.expect_const]
  have hsingle_nonneg (ℓ : X.Key) : 0 ≤ (Q ℓ).expect (L ℓ) := by
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro θ _
    apply mul_nonneg ((Q ℓ).nonneg θ)
    dsimp [L]
    split_ifs
    · unfold Setup5.colLik
      apply Finset.prod_nonneg
      intro h _
      exact Lane_q_s05_hist1b.ratio5_nonneg
        ((X.priorRep b ℓ K.1.1 z).nonneg _) ((X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)).nonneg _)
    · norm_num
  calc
    _ = (FinProb.pi Q).expect (fun U => ∏ ℓ, L ℓ (U ℓ)) := by
      simp only [hL]; rfl
    _ = ∏ ℓ, (Q ℓ).expect (L ℓ) := by
      unfold FinProb.expect FinProb.pi
      simp_rw [← Finset.prod_mul_distrib]
      rw [Fintype.prod_sum]
    _ ≤ ∏ _ℓ : X.Key, (1 : ℝ) :=
      Finset.prod_le_prod₀ (fun ℓ _ => hsingle_nonneg ℓ) (fun ℓ _ => hsingle ℓ)
    _ = 1 := by simp

theorem deleted_mass_integral (b : X.Base) (K : X.Ty) (keys : Finset X.Key) :
    (deletedHidden X b K).expect (fun U => X.blockMass (b, U) K keys) ≤ 1 := by
  unfold FinProb.expect Setup5.blockMass Setup5.blockWeight
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, X.blockBase b K z * (if X.blockGate b K z then 1 else 0) *
        (deletedHidden X b K).expect (fun U => ∏ ℓ ∈ keys, X.colLik b K ℓ z (U ℓ)) := by
      apply Finset.sum_congr rfl
      intro z _
      unfold FinProb.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U _
      ring
    _ ≤ ∑ z, X.blockBase b K z := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hg : X.blockGate b K z
      · simp only [if_pos hg, mul_one]
        exact mul_le_of_le_one_right
          (Finset.prod_nonneg fun _ _ => (X.segLaw b.1 (b.2.1 K.1.1)).nonneg _)
          (deleted_likelihood_integral X b K keys z)
      · simp only [if_neg hg, mul_zero, zero_mul]
        exact Finset.prod_nonneg fun _ _ => (X.segLaw b.1 (b.2.1 K.1.1)).nonneg _
    _ = 1 := blockBase_sum X b K

/-- Gate coverage depends only on a key's coarse part and level, not its sign. -/
def GateCovered (K : X.Ty) (keys : Finset X.Key) : Prop :=
  ∀ ℓ ∈ keys, ∃ ℓ' ∈ X.gateKeys K, ℓ.coarse = ℓ'.coarse ∧ ℓ.level = ℓ'.level

theorem column_recompose (b : X.Base) (K : X.Ty) (z : X.Block K) (ℓ : X.Key)
    (hℓ : ∃ ℓ' ∈ X.gateKeys K, ℓ.coarse = ℓ'.coarse ∧ ℓ.level = ℓ'.level)
    (hg : X.blockGate b K z) (θ : Fin (colLen5 (X.p.s n) ℓ) → Fin N) :
    (FinProb.pi fun _ => X.prior (putBlock X b K z) ℓ).w θ =
      (FinProb.pi fun _ => X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)).w θ *
        X.colLik b K ℓ z θ := by
  obtain ⟨ℓ', hℓ', hc, hl⟩ := hℓ
  have hrep : X.priorRep b ℓ K.1.1 z = X.priorRep b ℓ' K.1.1 z := by
    unfold Setup5.priorRep
    congr 1
    funext y
    simp [Setup5.colWeight, hc, hl]
  have hdel : X.priorDel b ℓ K.1.1 (X.p.typeSegs n K) =
      X.priorDel b ℓ' K.1.1 (X.p.typeSegs n K) := by
    unfold Setup5.priorDel
    congr 1
    funext y
    simp [Setup5.colWeight, hc, hl]
  have hprior : X.prior (putBlock X b K z) ℓ = X.priorRep b ℓ K.1.1 z := rfl
  let P := X.priorRep b ℓ K.1.1 z
  let Q := X.priorDel b ℓ K.1.1 (X.p.typeSegs n K)
  have hsupp (y : Fin N) (hy : Q.w y = 0) : P.w y = 0 := by
    have hd := hg ℓ' hℓ' y
    rw [← hrep, ← hdel] at hd
    have hp : P.w y ≤ 0 := by simpa [P, Q, hy] using hd
    exact le_antisymm hp (P.nonneg y)
  simp only [FinProb.pi, hprior, Setup5.colLik]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  exact (Lane_q_s05_hist1b.posterior_density_recompose5 P Q hsupp (θ h)).symm

theorem gated_hidden_pr (b : X.Base) (K : X.Ty) (z : X.Block K)
    (keys : Finset X.Key) (hkeys : GateCovered X K keys) (A : X.Hidden → Prop)
    (hA : FinProb.DependsOn (fun U => if A U then (1 : ℝ) else 0) keys) :
    (X.hiddenLaw (putBlock X b K z)).pr (fun U => X.blockGate b K z ∧ A U) =
      (deletedHidden X b K).expect (fun U =>
        if X.blockGate b K z ∧ A U then ∏ ℓ ∈ keys, X.colLik b K ℓ z (U ℓ) else 0) := by
  by_cases hg : X.blockGate b K z
  · have h := pi_change_weights
      (fun ℓ => FinProb.pi fun _ => X.prior (putBlock X b K z) ℓ)
      (fun ℓ => FinProb.pi fun _ => X.priorDel b ℓ K.1.1 (X.p.typeSegs n K))
      keys (fun ℓ θ => X.colLik b K ℓ z θ)
      (fun U => if A U then 1 else 0) (fun _ _ => X.y₀) hA
      (fun ℓ hℓ θ => column_recompose X b K z ℓ (hkeys ℓ hℓ) hg θ)
    simpa only [Setup5.hiddenLaw, deletedHidden, FinProb.pr, FinProb.expect,
      hg, true_and, mul_ite, mul_one, mul_zero] using h
  · simp [hg, FinProb.pr, FinProb.expect]

theorem local_lower_tail (b : X.Base) (K : X.Ty) (keys : Finset X.Key)
    (hkeys : GateCovered X K keys) (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ z, X.blockBase b K z * (X.hiddenLaw (putBlock X b K z)).pr
      (fun U => X.blockGate b K z ∧ X.blockMass (b, U) K keys < ε)) ≤ ε := by
  let P : FinProb (X.Block K) := FinProb.pi fun _ => X.segLaw b.1 (b.2.1 K.1.1)
  let Q := deletedHidden X b K
  let L : X.Block K → X.Hidden → ℝ := fun z U => ∏ ℓ ∈ keys, X.colLik b K ℓ z (U ℓ)
  have hm (U : X.Hidden) : X.blockMass (b, U) K keys =
      ∑ z, if X.blockGate b K z then P.w z * L z U else 0 := by
    unfold Setup5.blockMass Setup5.blockWeight
    apply Finset.sum_congr rfl
    intro z _
    by_cases hg : X.blockGate b K z <;> simp [hg, P, FinProb.pi, Setup5.blockBase, L]
  have hA : FinProb.DependsOn
      (fun U : X.Hidden => if X.blockMass (b, U) K keys < ε then (1 : ℝ) else 0) keys := by
    intro U V hUV
    dsimp only
    rw [blockMass_hidden_congr X b U V K keys hUV]
  have h := Lane_q_s05_hist1b.finite_subdensity_lower_bad5 P Q L
    (X.blockGate b K) (fun U => X.blockMass (b, U) K keys) ε hm hε
  convert h using 1
  apply Finset.sum_congr rfl
  intro z _
  rw [gated_hidden_pr X b K z keys hkeys _ hA]
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  by_cases ht : X.blockGate b K z ∧ X.blockMass (b, U) K keys < ε <;>
    simp [ht, P, Q, L, FinProb.pi, Setup5.blockBase] <;> ring

theorem local_ratio_tail (b : X.Base) (K : X.Ty) (keys del : Finset X.Key)
    (hkeys : GateCovered X K keys) (hdel : del ⊆ keys) (ε : ℝ) (hε : 0 ≤ ε) :
    (∑ z, X.blockBase b K z * (X.hiddenLaw (putBlock X b K z)).pr
      (fun U => X.blockGate b K z ∧
        X.blockMass (b, U) K keys < ε * X.blockMass (b, U) K del)) ≤ ε := by
  let P : FinProb (X.Block K) := FinProb.pi fun _ => X.segLaw b.1 (b.2.1 K.1.1)
  let Q := deletedHidden X b K
  let L : X.Block K → X.Hidden → ℝ := fun z U => ∏ ℓ ∈ keys, X.colLik b K ℓ z (U ℓ)
  have hm (U : X.Hidden) : X.blockMass (b, U) K keys =
      ∑ z, if X.blockGate b K z then P.w z * L z U else 0 := by
    unfold Setup5.blockMass Setup5.blockWeight
    apply Finset.sum_congr rfl
    intro z _
    by_cases hg : X.blockGate b K z <;> simp [hg, P, FinProb.pi, Setup5.blockBase, L]
  have hd (U : X.Hidden) : 0 ≤ X.blockMass (b, U) K del :=
    Finset.sum_nonneg fun z _ => Lane_q_s05_hist1b.blockWeight_nonneg X (b, U) K del z
  have hA : FinProb.DependsOn
      (fun U : X.Hidden => if X.blockMass (b, U) K keys < ε * X.blockMass (b, U) K del
        then (1 : ℝ) else 0) keys := by
    intro U V hUV
    dsimp only
    rw [blockMass_hidden_congr X b U V K keys hUV,
      blockMass_hidden_congr X b U V K del (fun ℓ hℓ => hUV ℓ (hdel hℓ))]
  have h := Lane_q_s05_hist1b.finite_subdensity_ratio_bad5 P Q L
    (X.blockGate b K) (fun U => X.blockMass (b, U) K keys)
    (fun U => X.blockMass (b, U) K del) ε hm hd (deleted_mass_integral X b K del) hε
  convert h using 1
  apply Finset.sum_congr rfl
  intro z _
  rw [gated_hidden_pr X b K z keys hkeys _ hA]
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  by_cases ht : X.blockGate b K z ∧
      X.blockMass (b, U) K keys < ε * X.blockMass (b, U) K del <;>
    simp [ht, P, Q, L, FinProb.pi, Setup5.blockBase] <;> ring

theorem raw_lower_tail (K : X.Ty) (keys : Finset X.Key)
    (hkeys : GateCovered X K keys) (ε : ℝ) (hε : 0 ≤ ε) :
    X.keyLaw.pr (fun H => X.blockGate H.1 K (X.trueBlock H.1 K) ∧
      X.blockMass H K keys < ε) ≤ ε := by
  let f : X.Base → ℝ := fun b => (X.hiddenLaw b).pr (fun U =>
    X.blockGate b K (X.trueBlock b K) ∧ X.blockMass (b, U) K keys < ε)
  have heq : X.keyLaw.pr (fun H => X.blockGate H.1 K (X.trueBlock H.1 K) ∧
      X.blockMass H K keys < ε) = X.baseLaw.expect f := by
    unfold Setup5.keyLaw FinProb.pr
    simp only [FinProb.bind]
    rw [Fintype.sum_prod_type]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [f]
    unfold FinProb.pr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    split_ifs <;> simp
  rw [heq, base_expect_resample X K f]
  calc
    _ ≤ X.baseLaw.expect (fun _ => ε) := by
      apply FinProb.expect_mono
      intro b
      simpa only [f, trueBlock_putBlock, blockGate_putBlock, blockMass_putBlock] using
        local_lower_tail X b K keys hkeys ε hε
    _ = ε := X.baseLaw.expect_const ε

theorem raw_ratio_tail (K : X.Ty) (keys del : Finset X.Key)
    (hkeys : GateCovered X K keys) (hdel : del ⊆ keys) (ε : ℝ) (hε : 0 ≤ ε) :
    X.keyLaw.pr (fun H => X.blockGate H.1 K (X.trueBlock H.1 K) ∧
      X.blockMass H K keys < ε * X.blockMass H K del) ≤ ε := by
  let f : X.Base → ℝ := fun b => (X.hiddenLaw b).pr (fun U =>
    X.blockGate b K (X.trueBlock b K) ∧
      X.blockMass (b, U) K keys < ε * X.blockMass (b, U) K del)
  have heq : X.keyLaw.pr (fun H => X.blockGate H.1 K (X.trueBlock H.1 K) ∧
      X.blockMass H K keys < ε * X.blockMass H K del) = X.baseLaw.expect f := by
    unfold Setup5.keyLaw FinProb.pr
    simp only [FinProb.bind]
    rw [Fintype.sum_prod_type]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [f]
    unfold FinProb.pr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U _
    split_ifs <;> simp
  rw [heq, base_expect_resample X K f]
  calc
    _ ≤ X.baseLaw.expect (fun _ => ε) := by
      apply FinProb.expect_mono
      intro b
      simpa only [f, trueBlock_putBlock, blockGate_putBlock, blockMass_putBlock] using
        local_ratio_tail X b K keys del hkeys hdel ε hε
    _ = ε := X.baseLaw.expect_const ε

theorem listed_gateCovered (K : X.Ty) : GateCovered X K K.2.1 := by
  intro ℓ hℓ
  exact ⟨ℓ, Finset.mem_union_left _ hℓ, rfl, rfl⟩

theorem optional_gateCovered (K : X.Ty) (t : CubeVertex (X.p.m n)) (hK : K.2.2 = none) :
    GateCovered X K (insert (X.optKeyOf K t) K.2.1) := by
  intro ℓ hℓ
  rcases Finset.mem_insert.mp hℓ with rfl | hℓ
  · refine ⟨.inl (K.1, fun _ => false, ⟨X.p.J n, Nat.lt_succ_self _⟩), ?_, rfl, rfl⟩
    simp [Setup5.gateKeys, hK]
  · exact listed_gateCovered X K ℓ hℓ

private theorem prob_le_one {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A ≤ 1 := by
  unfold FinProb.pr
  calc
    _ ≤ ∑ x, P.w x := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> simp [P.nonneg]
    _ = 1 := P.sum_eq_one

private theorem prob_mono {Ω : Type*} [Fintype Ω] (P : FinProb Ω)
    (A B : Ω → Prop) (h : ∀ x, A x → B x) : P.pr A ≤ P.pr B := by
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : A x
  · simp [ha, h x ha]
  · simp only [if_neg ha]
    split_ifs <;> simp [P.nonneg]

theorem typeKeys_nonempty (K : X.Ty) (hK : X.TypeOccurs K) : K.2.1.Nonempty := by
  obtain ⟨x, _, rfl⟩ := hK
  change (X.g.typeKeys (X.p.J n) x).Nonempty
  by_cases hx : X.g.severity x ≤ X.p.J n
  · refine ⟨keyAt5 (X.p.J n) (X.g.key x) (X.g.sign x) (X.g.severity x), ?_⟩
    simp only [ChunkGeometry5.typeKeys, if_pos hx, Finset.mem_union, Finset.mem_image]
    left; left
    exact ⟨X.g.key x, by simp [ChunkGeometry5.coarseRange], rfl⟩
  · refine ⟨.inr (X.g.key x), ?_⟩
    simp only [ChunkGeometry5.typeKeys, if_neg hx, Finset.mem_image]
    exact ⟨X.g.key x, by simp [ChunkGeometry5.coarseRange], rfl⟩

theorem colLen_pos_of_typeSegs_pos (K : X.Ty) (hk : 0 < X.p.typeSegs n K) (ℓ : X.Key) :
    1 ≤ colLen5 (X.p.s n) ℓ := by
  have hm : 2 ≤ X.p.m n := by
    by_contra hm
    have h01 : X.p.m n = 0 ∨ X.p.m n = 1 := by omega
    rcases h01 with hm | hm <;>
      cases htype : K.2.2 <;>
      simp [Params5.typeSegs, Params5.uSeg, Params5.uStarSeg, hm, htype] at hk
  cases ℓ with
  | inl k => simp [colLen5]
  | inr i =>
    have hmR : (1 : ℝ) < X.p.m n := by exact_mod_cast (show 1 < X.p.m n by omega)
    have hlog : 0 < Real.log (X.p.m n : ℝ) := Real.log_pos hmR
    have hpow : 1 ≤ (X.p.m n : ℝ) ^ (1 / 20 : ℝ) :=
      Real.one_le_rpow hmR.le (by norm_num)
    have hJ : 1 ≤ X.p.J n := by
      apply Nat.le_floor
      simpa only [Nat.cast_one] using hpow
    have hJR : (0 : ℝ) < X.p.J n := by exact_mod_cast (show 0 < X.p.J n by omega)
    have hs : 0 < X.p.s n := by
      apply Nat.ceil_pos.mpr
      exact mul_pos (mul_pos X.p.hKs hJR) hlog
    change 1 ≤ X.p.s n
    exact Nat.succ_le_iff.mpr hs

theorem step2_type_bound (K : X.Ty) (hK : X.TypeOccurs K) :
    X.keyLaw.pr (fun H => X.step2Fail H K) ≤
      ((K.2.1.card : ℝ) + 1) * Real.exp (-(X.p.delta * (X.p.q0 * X.p.typeSegs n K))) := by
  by_cases hk : X.p.typeSegs n K = 0
  · simp only [hk, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact (prob_le_one X.keyLaw _).trans (by
      have hc : (0 : ℝ) ≤ (K.2.1.card : ℝ) := Nat.cast_nonneg _
      linarith)
  have hkpos : 0 < X.p.typeSegs n K := Nat.pos_of_ne_zero hk
  let d : ℝ := X.p.delta * (X.p.q0 * X.p.typeSegs n K)
  let eps : ℝ := Real.exp (-d)
  let A : X.KeyHist → Prop := fun H => X.blockGate H.1 K (X.trueBlock H.1 K) ∧
    X.blockMass H K K.2.1 < Real.exp (-d * ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))
  let B : {ℓ // ℓ ∈ K.2.1} → X.KeyHist → Prop := fun ℓ H =>
    X.blockGate H.1 K (X.trueBlock H.1 K) ∧
      X.blockMass H K K.2.1 < Real.exp (-d * colLen5 (X.p.s n) ℓ.1) *
        X.blockMass H K (K.2.1.erase ℓ.1)
  have hd : 0 ≤ d := mul_nonneg X.p.hdelta.1.le (by positivity)
  have hsev : 1 ≤ ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ) := by
    obtain ⟨ℓ, hℓ⟩ := typeKeys_nonempty X K hK
    have hl : (1 : ℝ) ≤ colLen5 (X.p.s n) ℓ := by
      exact_mod_cast colLen_pos_of_typeSegs_pos X K hkpos ℓ
    exact hl.trans (Finset.single_le_sum (fun i _ => Nat.cast_nonneg _) hℓ)
  have hA : X.keyLaw.pr A ≤ eps := by
    have h := raw_lower_tail X K K.2.1 (listed_gateCovered X K)
      (Real.exp (-d * ∑ ℓ ∈ K.2.1, (colLen5 (X.p.s n) ℓ : ℝ))) (Real.exp_pos _).le
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hB (ℓ : {ℓ // ℓ ∈ K.2.1}) : X.keyLaw.pr (B ℓ) ≤ eps := by
    have hl : (1 : ℝ) ≤ colLen5 (X.p.s n) ℓ.1 := by
      exact_mod_cast colLen_pos_of_typeSegs_pos X K hkpos ℓ.1
    have h := raw_ratio_tail X K K.2.1 (K.2.1.erase ℓ.1) (listed_gateCovered X K)
      (Finset.erase_subset _ _) (Real.exp (-d * colLen5 (X.p.s n) ℓ.1)) (Real.exp_pos _).le
    exact h.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hcover (H : X.KeyHist) : X.step2Fail H K → A H ∨ ∃ ℓ, B ℓ H := by
    rintro ⟨hg, hlow | ⟨ℓ, hℓ, hratio⟩⟩
    · exact Or.inl ⟨hg, hlow⟩
    · exact Or.inr ⟨⟨ℓ, hℓ⟩, hg, hratio⟩
  calc
    _ ≤ X.keyLaw.pr (fun H => A H ∨ ∃ ℓ, B ℓ H) := prob_mono X.keyLaw _ _ hcover
    _ ≤ X.keyLaw.pr A + X.keyLaw.pr (fun H => ∃ ℓ, B ℓ H) := X.keyLaw.pr_union _ _
    _ ≤ eps + ∑ ℓ, X.keyLaw.pr (B ℓ) :=
      add_le_add hA (FinProb.pr_exists_le_sum5 X.keyLaw B)
    _ ≤ eps + ∑ _ℓ : {ℓ // ℓ ∈ K.2.1}, eps :=
      add_le_add (le_refl eps) (Finset.sum_le_sum fun ℓ _ => hB ℓ)
    _ = _ := by simp [eps, d]; ring

theorem step2_optional_bound (K : X.Ty) (t : CubeVertex (X.p.m n))
    (hKt : X.OptOccurs K t) : X.keyLaw.pr (fun H => X.optFail H K t) ≤
      Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n))) := by
  obtain ⟨x, _, hx, ho⟩ := hKt
  have hK : K.2.2 = none := by
    have hj : X.g.severity x = X.p.J n + 1 := by
      by_contra hj
      simp [ChunkGeometry5.optionalKey, hj] at ho
    rw [← hx]
    simp [ChunkGeometry5.evenType, hj]
  exact raw_ratio_tail X K (insert (X.optKeyOf K t) K.2.1) K.2.1
    (optional_gateCovered X K t hK) (Finset.subset_insert _ _)
    (Real.exp (-(X.p.delta * (X.p.q0 * X.p.uStarSeg n)))) (Real.exp_pos _).le

end
end HypercubeRamsey.Lane_sol_s05_hist1b
