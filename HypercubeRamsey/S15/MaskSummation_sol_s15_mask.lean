import HypercubeRamsey.S15.ClusterNodes_sol_s15_mask
import HypercubeRamsey.S15.MaskCounting_sol_s15_mask
import HypercubeRamsey.S15.DirectNodes_q_s15_direct

namespace HypercubeRamsey.Lane_sol_s15_mask

open HypercubeRamsey.S15 Classical
open scoped BigOperators

def PatchTuple {ι α : Type*} (S : Finset α) (vs : ι → α) : Prop :=
  ∀ r, vs r ∈ S

theorem sum_patch_tuples {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    (S : Finset α) (F : (ι → α) → ℝ) :
    (∑ vs : ι → α, if PatchTuple S vs then F vs else 0) =
      ∑ vs : ι → {a : α // a ∈ S}, F (fun r => (vs r).1) := by
  let e : {vs : ι → α // ∀ r, vs r ∈ S} ≃ (ι → {a : α // a ∈ S}) :=
    Equiv.subtypePiEquivPi
  calc
    _ = ∑ vs : {vs : ι → α // ∀ r, vs r ∈ S}, F vs.1 := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun vs => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl) _
    _ = _ := Fintype.sum_equiv e _ _ (fun vs => rfl)

theorem rank_depends_kept {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (G : Finset (Fin (T.S.n k)))
    (vs ws : Fin (T.S.n k) → EvenPosition T k)
    (h : ∀ r, r ∉ G → vs r = ws r) :
    clusterCrossingRank PT vs G = clusterCrossingRank PT ws G := by
  have hedge : clusterCrossingEdge PT vs G = clusterCrossingEdge PT ws G := by
    funext r t
    apply propext
    by_cases hr : r ∈ G
    · simp only [clusterCrossingEdge, hr, not_true_eq_false, false_and]
    · by_cases ht : t ∈ G
      · simp only [clusterCrossingEdge, ht, not_true_eq_false, false_and, and_false]
      · simp only [clusterCrossingEdge, h r hr, h t ht]
  simp only [clusterCrossingRank, hedge]

theorem rank_update_removed {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (G : Finset (Fin (T.S.n k)))
    (r : Fin (T.S.n k)) (hr : r ∈ G)
    (vs : Fin (T.S.n k) → EvenPosition T k) (a : EvenPosition T k) :
    clusterCrossingRank PT (Function.update vs r a) G = clusterCrossingRank PT vs G := by
  apply rank_depends_kept
  intro t ht
  have htne : t ≠ r := by intro heq; subst t; exact ht hr
  exact Function.update_of_ne htne _ _

theorem crossing_queries_card {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (M : ClusterMask PT) :
    (clusterAllowedCrossings PT hPT M).card ≤ (T.S.n k) ^ 2 := by
  let all := Finset.univ.biUnion fun r : Fin (T.S.n k) =>
    (clusterCrossingNeighbours PT hPT (M.positions r)).image (fun b => (r, b))
  have hsub : clusterAllowedCrossings PT hPT M ⊆ all := by
    intro q hq
    have hq' := (Finset.mem_filter.mp hq).2.2.2
    exact Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨q.2, hq', rfl⟩⟩
  have hstar (r : Fin (T.S.n k)) :
      (clusterCrossingNeighbours PT hPT (M.positions r)).card ≤ T.S.n k := by
    calc
      _ ≤ (Lane_q_s15_direct.star (M.positions r)).card := by
        apply Finset.card_le_card
        intro b hb
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.1⟩
      _ ≤ _ := Lane_q_s15_direct.star_card_le _
  calc
    _ ≤ all.card := Finset.card_le_card hsub
    _ ≤ ∑ r : Fin (T.S.n k),
        ((clusterCrossingNeighbours PT hPT (M.positions r)).image (fun b => (r, b))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r : Fin (T.S.n k), T.S.n k := by
      apply Finset.sum_le_sum
      intro r hr
      exact (Finset.card_image_le).trans (hstar r)
    _ = _ := by simp [pow_two]

theorem subset_power_sum {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (q : ℝ) :
    (∑ D : Finset α, if D ⊆ S then q ^ D.card else 0) = (1 + q) ^ S.card := by
  calc
    _ = ∑ D ∈ S.powerset, q ^ D.card := by
      simp only [← Finset.mem_powerset]
      exact Finset.sum_ite_mem_eq _ _
    _ = _ := by
      simpa only [Finset.prod_const] using
        (Finset.prod_one_add (f := fun _ : α => q) S).symm

theorem all_subset_power_sum {α : Type*} [Fintype α] [DecidableEq α] (q : ℝ) :
    (∑ D : Finset α, q ^ D.card) = (1 + q) ^ Fintype.card α := by
  simpa only [Finset.subset_univ, ↓reduceIte, Finset.card_univ] using
    subset_power_sum (Finset.univ : Finset α) q

theorem rank_tail_subtype {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (G : Finset (Fin (T.S.n k))) (j : ℕ) :
    clusterCrossingRankTail PT i G j =
      (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ *
        ∑ vs : Fin (T.S.n k) → {a : EvenPosition T k // a ∈ evenPatchPositions PT.tiling i},
          if j ≤ clusterCrossingRank PT (fun r => (vs r).1) G then 1 else 0 := by
  unfold clusterCrossingRankTail
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  calc
    _ = ∑ vs, if PatchTuple (evenPatchPositions PT.tiling i) vs then
        (if j ≤ clusterCrossingRank PT vs G then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro vs hvs
      by_cases hp : PatchTuple (evenPatchPositions PT.tiling i) vs
      · have hp' : ∀ r, vs r ∈ evenPatchPositions PT.tiling i := hp
        by_cases hj : j ≤ clusterCrossingRank PT vs G <;> simp [hp, hp', hj]
      · have hp' : ¬ ∀ r, vs r ∈ evenPatchPositions PT.tiling i := hp
        by_cases hj : j ≤ clusterCrossingRank PT vs G <;> simp [hp, hp', hj]
    _ = _ := sum_patch_tuples (ι := Fin (T.S.n k)) (evenPatchPositions PT.tiling i)
      (fun vs => if j ≤ clusterCrossingRank PT vs G then (1 : ℝ) else 0)

theorem rank_average_le_two {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m)
    (G : Finset (Fin (T.S.n k))) (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hat : a * t ≤ 1 / 2)
    (htail : ∀ j ≤ T.S.n k, clusterCrossingRankTail PT i G j ≤ t ^ j) :
    (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ *
      (∑ vs : Fin (T.S.n k) → {a : EvenPosition T k // a ∈ evenPatchPositions PT.tiling i},
        a ^ clusterCrossingRank PT (fun r => (vs r).1) G) ≤ 2 := by
  let U := {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i}
  let w : (Fin (T.S.n k) → U) → ℝ := fun _ =>
    (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹
  let rank : (Fin (T.S.n k) → U) → ℕ := fun vs =>
    clusterCrossingRank PT (fun r => (vs r).1) G
  have hw : ∀ vs, 0 ≤ w vs := fun _ => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  have hr : ∀ vs, rank vs ≤ T.S.n k := fun vs => Nat.sub_le _ _
  have htail' : ∀ j ≤ T.S.n k,
      (∑ vs : Fin (T.S.n k) → U, w vs * (if j ≤ rank vs then 1 else 0)) ≤ t ^ j := by
    intro j hj
    dsimp only [w, rank, U]
    rw [← Finset.mul_sum]
    have hh := htail j hj
    rw [rank_tail_subtype] at hh
    exact hh
  have hh := weighted_rank_moment w hw rank (T.S.n k) hr a t ha htail'
  rw [← Finset.mul_sum] at hh
  exact hh.trans (geometric_sum_le_two (a * t) (mul_nonneg ha ht) hat _)

theorem near_subtype_card {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (near : α → α → Prop) (a : {v : α // v ∈ S}) :
    (Finset.univ.filter (fun b : {v : α // v ∈ S} => near a.1 b.1)).card =
      (S.filter (near a.1)).card := by
  let e : {b : {v : α // v ∈ S} // near a.1 b.1} ≃
      {b : α // b ∈ S.filter (near a.1)} :=
    { toFun := fun b => ⟨b.1.1, Finset.mem_filter.mpr ⟨b.1.2, b.2⟩⟩
      invFun := fun b => ⟨⟨b.1, (Finset.mem_filter.mp b.2).1⟩, (Finset.mem_filter.mp b.2).2⟩
      left_inv := fun b => rfl
      right_inv := fun b => rfl }
  calc
    _ = Fintype.card {b : {v : α // v ∈ S} // near a.1 b.1} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {b : α // b ∈ S.filter (near a.1)} := Fintype.card_congr e
    _ = _ := Fintype.card_coe _

theorem geometric_removed_rank_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (hS : (evenPatchPositions PT.tiling i).Nonempty)
    (G : Finset (Fin (T.S.n k))) (a f : ℝ) (ha : 0 ≤ a) (hf : 0 ≤ f)
    (hcore : ∀ v ∈ evenPatchPositions PT.tiling i,
      (((evenPatchPositions PT.tiling i).filter (clusterCoreNear PT hPT i v)).card : ℝ) ≤
        f * (evenPatchPositions PT.tiling i).card)
    (hrank : (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ *
      (∑ vs : Fin (T.S.n k) → {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i},
        a ^ clusterCrossingRank PT (fun r => (vs r).1) G) ≤ 2) :
    (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ *
      (∑ vs : Fin (T.S.n k) → {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i},
        if NecessaryNear (fun v w => clusterCoreNear PT hPT i v.1 w.1) G vs then
          a ^ clusterCrossingRank PT (fun r => (vs r).1) G else 0) ≤
        ((T.S.n k : ℝ) * f) ^ G.card * 2 := by
  let U := {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i}
  letI : Nonempty U := by obtain ⟨v, hv⟩ := hS; exact ⟨⟨v, hv⟩⟩
  let near : U → U → Prop := fun v w => clusterCoreNear PT hPT i v.1 w.1
  let F : (Fin (T.S.n k) → U) → ℝ := fun vs =>
    a ^ clusterCrossingRank PT (fun r => (vs r).1) G
  have hF0 : ∀ vs, 0 ≤ F vs := fun _ => pow_nonneg ha _
  have hF : ∀ r ∈ G, ∀ vs u, F (Function.update vs r u) = F vs := by
    intro r hr vs u
    apply congrArg (fun j => a ^ j)
    apply rank_depends_kept
    intro t ht
    have htne : t ≠ r := by intro heq; subst t; exact ht hr
    rw [Function.update_of_ne htne]
  have hnear : ∀ v : U, ((Finset.univ.filter (near v)).card : ℝ) ≤ f * Fintype.card U := by
    intro v
    change ((Finset.univ.filter fun b : {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i} =>
      clusterCoreNear PT hPT i v.1 b.1).card : ℝ) ≤ f *
        Fintype.card {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i}
    rw [near_subtype_card, Fintype.card_coe]
    exact hcore v.1 v.2
  have hh := reverse_near_sum near G F hF0 hF f hf hnear
  have hd0 : 0 ≤ (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ ≤ (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ *
        (((T.S.n k : ℝ) * f) ^ G.card * ∑ vs, F vs) :=
      mul_le_mul_of_nonneg_left hh hd0
    _ = ((T.S.n k : ℝ) * f) ^ G.card *
        ((((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ * ∑ vs, F vs) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrank (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hf) _)

def ExactGeometric {U : Type*} {n : ℕ} (near : U → U → Prop)
    (G : Finset (Fin n)) (vs : Fin n → U) : Prop :=
  ∀ r, r ∈ G ↔ EarlierNear near vs r

theorem exactGeometric_necessary {U : Type*} {n : ℕ} (near : U → U → Prop)
    (G : Finset (Fin n)) (vs : Fin n → U) (h : ExactGeometric near G vs) :
    NecessaryNear near G vs := fun r hr => (h r).mp hr

theorem crossing_subset_sum_le {β : Type*} [Fintype β] [DecidableEq β]
    (R : Finset β) (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (hR : R.card ≤ n ^ 2) (hsmall : q * (n : ℝ) ^ 2 ≤ 1) :
    (∑ Q : Finset β, if Q ⊆ R then q ^ Q.card else 0) ≤ Real.exp 1 := by
  calc
    _ = ∑ Q ∈ R.powerset, q ^ Q.card := by
      simp only [← Finset.mem_powerset]
      exact Finset.sum_ite_mem_eq _ _
    _ ≤ Real.exp (q * R.card) := Lane_q_s15_c3.finset_powerset_pow_le_exp R q hq
    _ ≤ Real.exp 1 := by
      apply Real.exp_le_exp.mpr
      calc
        q * R.card ≤ q * (n : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hq
          exact_mod_cast hR
        _ ≤ _ := hsmall

theorem finite_ordered_mask_sum {U β : Type*} [Fintype U] [Nonempty U]
    [Fintype β] [DecidableEq β] (n : ℕ) (near : U → U → Prop)
    (rank : (Fin n → U) → Finset (Fin n) → ℕ)
    (R : (Fin n → U) → Finset (Fin n) → Finset (Fin n) → Finset β)
    (A B q a f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hf : 0 ≤ f)
    (hnear : ∀ v, ((Finset.univ.filter (near v)).card : ℝ) ≤ f * Fintype.card U)
    (hdep : ∀ G r, r ∈ G → ∀ vs u, rank (Function.update vs r u) G = rank vs G)
    (hrank : ∀ G, ((Fintype.card U : ℝ) ^ n)⁻¹ * (∑ vs, a ^ rank vs G) ≤ 2)
    (hR : ∀ vs G C, (R vs G C).card ≤ n ^ 2)
    (hsmall : q * (n : ℝ) ^ 2 ≤ 1) :
    ((Fintype.card U : ℝ) ^ n)⁻¹ *
      (∑ vs : Fin n → U, ∑ G : Finset (Fin n), ∑ C : Finset (Fin n), ∑ Q : Finset β,
        if ExactGeometric near G vs ∧ Disjoint G C ∧ Q ⊆ R vs G C then
          A ^ G.card * B ^ C.card * q ^ Q.card * a ^ rank vs G else 0) ≤
        2 * Real.exp 1 * (1 + B) ^ n * (1 + (n : ℝ) * f * A) ^ n := by
  let d : ℝ := (Fintype.card U : ℝ) ^ n
  have hd : 0 ≤ d⁻¹ := inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  have hinner (vs : Fin n → U) (G : Finset (Fin n)) :
      (∑ C : Finset (Fin n), ∑ Q : Finset β,
        if ExactGeometric near G vs ∧ Disjoint G C ∧ Q ⊆ R vs G C then
          A ^ G.card * B ^ C.card * q ^ Q.card * a ^ rank vs G else 0) ≤
        if ExactGeometric near G vs then
          (Real.exp 1 * (1 + B) ^ n) * (A ^ G.card * a ^ rank vs G) else 0 := by
    by_cases he : ExactGeometric near G vs
    · rw [if_pos he]
      calc
        _ ≤ ∑ C : Finset (Fin n),
            A ^ G.card * B ^ C.card * a ^ rank vs G * Real.exp 1 := by
          apply Finset.sum_le_sum
          intro C hC
          calc
            _ ≤ (A ^ G.card * B ^ C.card * a ^ rank vs G) *
                ∑ Q : Finset β, if Q ⊆ R vs G C then q ^ Q.card else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum
              intro Q hQ
              by_cases hsub : Q ⊆ R vs G C
              · rw [if_pos hsub]
                by_cases hdis : Disjoint G C
                · rw [if_pos ⟨he, hdis, hsub⟩]
                  ring_nf
                  exact le_rfl
                · rw [if_neg (by tauto)]
                  positivity
              · rw [if_neg hsub, if_neg (by tauto)]
                simp
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (crossing_subset_sum_le (R vs G C) q hq n (hR vs G C) hsmall) (by positivity)
        _ = _ := by
          have hc := all_subset_power_sum (α := Fin n) B
          calc
            _ = (A ^ G.card * a ^ rank vs G * Real.exp 1) * ∑ C : Finset (Fin n), B ^ C.card := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro C hC
              ring
            _ = _ := by rw [hc, Fintype.card_fin]; ring
    · simp only [he, false_and, ↓reduceIte, Finset.sum_const_zero]
      exact le_rfl
  have hgeom (G : Finset (Fin n)) :
      d⁻¹ * (∑ vs : Fin n → U, if ExactGeometric near G vs then
        A ^ G.card * a ^ rank vs G else 0) ≤
          2 * ((n : ℝ) * f * A) ^ G.card := by
    have hF0 : ∀ vs : Fin n → U, 0 ≤ a ^ rank vs G := fun _ => pow_nonneg ha _
    have hrev := reverse_near_sum near G (fun vs => a ^ rank vs G) hF0
      (fun r hr vs u => congrArg (fun j => a ^ j) (hdep G r hr vs u)) f hf hnear
    have hdrop : (∑ vs : Fin n → U, if ExactGeometric near G vs then a ^ rank vs G else 0) ≤
        ∑ vs : Fin n → U, if NecessaryNear near G vs then a ^ rank vs G else 0 := by
      apply Finset.sum_le_sum
      intro vs hvs
      by_cases he : ExactGeometric near G vs
      · simp only [if_pos he, if_pos (exactGeometric_necessary near G vs he)]
        exact le_rfl
      · rw [if_neg he]
        split_ifs <;> simp [hF0]
    calc
      _ = A ^ G.card * (d⁻¹ * ∑ vs : Fin n → U,
          if ExactGeometric near G vs then a ^ rank vs G else 0) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro vs hvs
        split_ifs <;> ring
      _ ≤ A ^ G.card * (d⁻¹ *
          (((n : ℝ) * f) ^ G.card * ∑ vs, a ^ rank vs G)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hdrop.trans hrev) hd) (pow_nonneg hA _)
      _ = (A * ((n : ℝ) * f)) ^ G.card * (d⁻¹ * ∑ vs, a ^ rank vs G) := by
        rw [mul_pow]
        ring
      _ ≤ (A * ((n : ℝ) * f)) ^ G.card * 2 :=
        mul_le_mul_of_nonneg_left (hrank G) (by positivity)
      _ = _ := by rw [mul_comm A, mul_assoc]; ring
  calc
    _ ≤ d⁻¹ * ∑ vs : Fin n → U, ∑ G : Finset (Fin n),
        if ExactGeometric near G vs then
          (Real.exp 1 * (1 + B) ^ n) * (A ^ G.card * a ^ rank vs G) else 0 := by
      apply mul_le_mul_of_nonneg_left _ hd
      apply Finset.sum_le_sum
      intro vs hvs
      exact Finset.sum_le_sum fun G hG => hinner vs G
    _ = (Real.exp 1 * (1 + B) ^ n) * ∑ G : Finset (Fin n),
        d⁻¹ * (∑ vs : Fin n → U, if ExactGeometric near G vs then
          A ^ G.card * a ^ rank vs G else 0) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G hG
      apply Finset.sum_congr rfl
      intro vs hvs
      split_ifs <;> ring
    _ ≤ (Real.exp 1 * (1 + B) ^ n) *
        ∑ G : Finset (Fin n), 2 * ((n : ℝ) * f * A) ^ G.card := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun G hG => hgeom G
    _ = _ := by
      rw [← Finset.mul_sum, all_subset_power_sum, Fintype.card_fin]
      ring

theorem sum_masks {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (F : ClusterMask PT → ℝ) :
    (∑ M, F M) = ∑ vs : Fin (T.S.n k) → EvenPosition T k,
      ∑ G : Finset (Fin (T.S.n k)), ∑ C : Finset (Fin (T.S.n k)),
        ∑ Q : Finset (Fin (T.S.n k) × OddPosition T k), F ⟨vs, G, C, Q⟩ := by
  let e : ClusterMask PT ≃
      ((Fin (T.S.n k) → EvenPosition T k) × Finset (Fin (T.S.n k)) ×
        Finset (Fin (T.S.n k)) × Finset (Fin (T.S.n k) × OddPosition T k)) :=
    { toFun := fun M => (M.positions, M.geometric, M.coreBins, M.crossingBins)
      invFun := fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := by intro M; cases M; rfl
      right_inv := by intro p; rfl }
  calc
    _ = ∑ p, F (e.symm p) := Fintype.sum_equiv e _ _ (fun M => by cases M; rfl)
    _ = _ := by simp only [Fintype.sum_prod_type]; rfl

theorem allowed_crossings_mk {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (vs : Fin (T.S.n k) → EvenPosition T k)
    (G C : Finset (Fin (T.S.n k))) (Q : Finset (Fin (T.S.n k) × OddPosition T k)) :
    clusterAllowedCrossings PT hPT ⟨vs, G, C, Q⟩ =
      clusterAllowedCrossings PT hPT ⟨vs, G, C, ∅⟩ := by
  ext q
  simp [clusterAllowedCrossings, clusterKeptRows]

theorem mask_geometry_mk {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (vs : Fin (T.S.n k) → EvenPosition T k)
    (G C : Finset (Fin (T.S.n k))) (Q : Finset (Fin (T.S.n k) × OddPosition T k)) :
    ClusterMaskGeometry PT hPT i ⟨vs, G, C, Q⟩ ↔
      (∀ r, vs r ∈ evenPatchPositions PT.tiling i) ∧
        ExactGeometric (clusterCoreNear PT hPT i) G vs ∧ Disjoint G C ∧
          Q ⊆ clusterAllowedCrossings PT hPT ⟨vs, G, C, ∅⟩ := by
  unfold ClusterMaskGeometry
  rw [allowed_crossings_mk]
  rfl

theorem cluster_mask_weight_sum {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (hS : (evenPatchPositions PT.tiling i).Nonempty)
    (A B q a f : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (ha : 0 ≤ a) (hf : 0 ≤ f)
    (hcore : ∀ v ∈ evenPatchPositions PT.tiling i,
      (((evenPatchPositions PT.tiling i).filter (clusterCoreNear PT hPT i v)).card : ℝ) ≤
        f * (evenPatchPositions PT.tiling i).card)
    (hrank : ∀ G, (((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k))⁻¹ *
      (∑ vs : Fin (T.S.n k) → {v : EvenPosition T k // v ∈ evenPatchPositions PT.tiling i},
        a ^ clusterCrossingRank PT (fun r => (vs r).1) G) ≤ 2)
    (hsmall : q * (T.S.n k : ℝ) ^ 2 ≤ 1) :
    (∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then
      A ^ M.geometric.card * B ^ M.coreBins.card * q ^ M.crossingBins.card *
        a ^ clusterCrossingRank PT M.positions M.geometric else 0) /
      ((evenPatchPositions PT.tiling i).card : ℝ) ^ (T.S.n k) ≤
        2 * Real.exp 1 * (1 + B) ^ (T.S.n k) *
          (1 + (T.S.n k : ℝ) * f * A) ^ (T.S.n k) := by
  let S := evenPatchPositions PT.tiling i
  let U := {v : EvenPosition T k // v ∈ S}
  letI : Nonempty U := by obtain ⟨v, hv⟩ := hS; exact ⟨⟨v, hv⟩⟩
  let near : U → U → Prop := fun v w => clusterCoreNear PT hPT i v.1 w.1
  let rank : (Fin (T.S.n k) → U) → Finset (Fin (T.S.n k)) → ℕ :=
    fun vs G => clusterCrossingRank PT (fun r => (vs r).1) G
  let R := fun (vs : Fin (T.S.n k) → U) (G C : Finset (Fin (T.S.n k))) =>
    clusterAllowedCrossings PT hPT ⟨fun r => (vs r).1, G, C, ∅⟩
  have hnear : ∀ v : U, ((Finset.univ.filter (near v)).card : ℝ) ≤ f * Fintype.card U := by
    intro v
    change ((Finset.univ.filter fun b : {v : EvenPosition T k // v ∈ S} =>
      clusterCoreNear PT hPT i v.1 b.1).card : ℝ) ≤ f * Fintype.card {v : EvenPosition T k // v ∈ S}
    rw [near_subtype_card, Fintype.card_coe]
    exact hcore v.1 v.2
  have hdep : ∀ G r, r ∈ G → ∀ vs u, rank (Function.update vs r u) G = rank vs G := by
    intro G r hr vs u
    apply rank_depends_kept
    intro t ht
    have htne : t ≠ r := by intro heq; subst t; exact ht hr
    rw [Function.update_of_ne htne]
  have hrank' : ∀ G, ((Fintype.card U : ℝ) ^ (T.S.n k))⁻¹ * (∑ vs, a ^ rank vs G) ≤ 2 := by
    intro G
    simpa only [U, S, Fintype.card_coe] using hrank G
  have hh := finite_ordered_mask_sum (T.S.n k) near rank R A B q a f
    hA hB hq ha hf hnear hdep hrank'
    (fun vs G C => crossing_queries_card PT hPT _) hsmall
  have heq :
      (∑ M : ClusterMask PT, if ClusterMaskGeometry PT hPT i M then
        A ^ M.geometric.card * B ^ M.coreBins.card * q ^ M.crossingBins.card *
          a ^ clusterCrossingRank PT M.positions M.geometric else 0) =
      ∑ vs : Fin (T.S.n k) → U, ∑ G : Finset (Fin (T.S.n k)),
        ∑ C : Finset (Fin (T.S.n k)), ∑ Q : Finset (Fin (T.S.n k) × OddPosition T k),
          if ExactGeometric near G vs ∧ Disjoint G C ∧ Q ⊆ R vs G C then
            A ^ G.card * B ^ C.card * q ^ Q.card * a ^ rank vs G else 0 := by
    rw [sum_masks]
    calc
      _ = ∑ vs : Fin (T.S.n k) → EvenPosition T k,
          if PatchTuple S vs then
            (∑ G : Finset (Fin (T.S.n k)), ∑ C : Finset (Fin (T.S.n k)),
              ∑ Q : Finset (Fin (T.S.n k) × OddPosition T k),
                if ExactGeometric (clusterCoreNear PT hPT i) G vs ∧ Disjoint G C ∧
                  Q ⊆ clusterAllowedCrossings PT hPT ⟨vs, G, C, ∅⟩ then
                  A ^ G.card * B ^ C.card * q ^ Q.card * a ^ clusterCrossingRank PT vs G else 0)
          else 0 := by
        apply Finset.sum_congr rfl
        intro vs hvs
        by_cases hp : PatchTuple S vs
        · rw [if_pos hp]
          have hpfull : ∀ r, vs r ∈ evenPatchPositions PT.tiling i := hp
          apply Finset.sum_congr rfl
          intro G hG
          apply Finset.sum_congr rfl
          intro C hC
          apply Finset.sum_congr rfl
          intro Q hQ
          simp [mask_geometry_mk, hpfull]
        · rw [if_neg hp]
          have hpfull : ¬ ∀ r, vs r ∈ evenPatchPositions PT.tiling i := hp
          apply Finset.sum_eq_zero
          intro G hG
          apply Finset.sum_eq_zero
          intro C hC
          apply Finset.sum_eq_zero
          intro Q hQ
          simp only [mask_geometry_mk, hpfull, false_and, ↓reduceIte]
      _ = _ := sum_patch_tuples S _
  rw [heq, div_eq_mul_inv, mul_comm]
  simpa only [U, S, Fintype.card_coe] using hh

theorem coreRepeatCost_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) : 0 ≤ clusterCoreRepeatCost PT i := by
  unfold clusterCoreRepeatCost
  positivity

theorem masked_integral_large_zero {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (hs : PT.tiling.mode ≠ .highSmall)
    (hM : M.coreBins ≠ ∅ ∨ M.crossingBins ≠ ∅) : clusterMaskedIntegral CS i x M = 0 := by
  unfold clusterMaskedIntegral FinLaw.E
  apply Finset.sum_eq_zero
  intro ω hω
  have hnot : ¬ ClusterMaskConsistent PT hPT hm M (CS.bins ω) := by
    intro hc
    rw [ClusterMaskConsistent, if_neg hs] at hc
    rcases hM with hM | hM
    · exact hM hc.1
    · exact hM hc.2
  simp only [hnot, and_false, ↓reduceIte, mul_zero]

end HypercubeRamsey.Lane_sol_s15_mask
