import HypercubeRamsey.S18.Lists

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators

open S16.Lane_q_s16_comp2
set_option backward.isDefEq.respectTransparency false

theorem uniform_pi {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (d : ∀ i, Ω i) :
    FinLaw.uniform Finset.univ ⟨d, Finset.mem_univ _⟩ =
      FinLaw.pi (fun i => FinLaw.uniform Finset.univ ⟨d i, Finset.mem_univ _⟩) := by
  apply finLaw_ext
  intro x
  simp only [FinLaw.uniform, FinLaw.pi, Finset.mem_univ, if_true,
    Finset.card_univ, Fintype.card_pi, Nat.cast_prod, one_div, Finset.prod_inv_distrib]

theorem pi_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (d : ∀ i, Ω i) (i : I) (f : Ω i → ℝ) :
    (FinLaw.pi P).E (fun x => f (x i)) = (P i).E f := by
  let g : ∀ j, Ω j → ℝ := fun j z =>
    if j = i then f ((Function.update d j z) i) else 1
  have hprod (x : ∀ j, Ω j) : (∏ j, g j (x j)) = f (x i) := by
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro j _ hj
      simp [g, hj]
    · simp
  calc
    (FinLaw.pi P).E (fun x => f (x i)) =
        (FinLaw.pi P).E (fun x => ∏ j, g j (x j)) := by simp_rw [hprod]
    _ = ∏ j, (P j).E (g j) := pi_expect_prod P g
    _ = (P i).E f := by
      rw [Finset.prod_eq_single i]
      · simp [g]
      · intro j _ hj
        simp [g, hj, FinLaw.E, FinLaw.sum_one]
      · simp

theorem prod_consulted {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (c : A → I) (f : A → ℝ) :
    (∏ C ∈ (Finset.univ.filter fun C => ∃ a, c a = C),
      ∏ a : {a // c a = C}, f a.1) = ∏ a, f a := by
  rw [← Fintype.prod_fiberwise c f]
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro C _ hC
  have hnone : ¬ ∃ a, c a = C := by simpa using hC
  have hempty : IsEmpty {a // c a = C} := ⟨fun a => hnone ⟨a.1, a.2⟩⟩
  letI := hempty
  simp

theorem prod_typical {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (c : A → I) (S : Finset I) (hS : ∀ C, C ∈ S ↔ ∃ a, c a = C)
    (t : I → Prop) (v : I → ℝ) :
    (if ∀ a, t (c a) then
      ∏ C ∈ S, v C else 0) =
    ∏ C ∈ S, if t C then v C else 0 := by
  classical
  by_cases ht : ∀ a, t (c a)
  · rw [if_pos ht]
    apply Finset.prod_congr rfl
    intro C hC
    obtain ⟨a, rfl⟩ := (hS C).mp hC
    exact (if_pos (ht a)).symm
  · rw [if_neg ht]
    obtain ⟨a, ha⟩ := not_forall.mp ht
    symm
    apply Finset.prod_eq_zero (i := c a)
    · exact (hS (c a)).mpr ⟨a, rfl⟩
    · simp [ha]

theorem pi_consulted {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (S : Finset I) (f : ∀ i, Ω i → ℝ) :
    (FinLaw.pi P).E (fun x =>
      ∏ C ∈ S, f C (x C)) =
    ∏ C ∈ S, (P C).E (f C) := by
  let g : ∀ i, Ω i → ℝ := fun i z => if i ∈ S then f i z else 1
  have hp (x : ∀ i, Ω i) : (∏ i, g i (x i)) = ∏ i ∈ S, f i (x i) := by
    exact Finset.prod_ite_mem_eq S _
  have hE (i : I) : (P i).E (g i) = if i ∈ S then (P i).E (f i) else 1 := by
    by_cases hi : i ∈ S <;> simp [g, hi, FinLaw.E, FinLaw.sum_one]
  calc
    _ = (FinLaw.pi P).E (fun x => ∏ i, g i (x i)) := by
      change (FinLaw.pi P).E (fun x => ∏ i ∈ S, f i (x i)) = _
      simp_rw [hp]
    _ = ∏ i, (P i).E (g i) := pi_expect_prod P g
    _ = _ := by simp_rw [hE]; exact Finset.prod_ite_mem_eq S _

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

theorem Q0_pos (hκ : κ.Admissible) : 0 < κ.Q0 := by
  have hCb : 0 < κ.Cb := by
    have hd := div_pos (mul_pos (by norm_num : (0 : ℝ) < 100) hκ.aC_rng.1)
      hκ.aB_rng.1
    linarith [hκ.Cb_big]
  have hMlo : (0 : ℝ) < κ.Mlo := by linarith [hκ.Mlo_big]
  by_contra hQ
  have h := (hκ.Q0_large 0 (not_lt.mp hQ)).2.1
  simp only [Real.rpow_eq_pow, Real.zero_rpow (ne_of_gt hκ.aC_rng.1),
    Real.zero_rpow (ne_of_gt hMlo), mul_zero, zero_div, zero_add] at h
  norm_num at h

/-- The repaired contract now supplies the group-separation margin on each
actual low-cluster patch. -/
theorem patch_threshold (hκ : κ.Admissible) (hT : LateThresholds κ)
    (hPT : PT.Valid) (hm : PT.tiling.mode = .lowCluster) (i : Fin PT.tiling.m) :
    2 < 20 * κ.ρ * (PT.tiling.P i).h := by
  rcases hPT.tiling_valid.cluster_data (Or.inl hm) i with
    ⟨hthreshold, hgq, hmass, hsmall, hbin, hcodeg, hdyadic, hhl, hrest⟩
  have hM : 0 < κ.M1 := by linarith [hκ.M1_big.1]
  have hmax : max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) ≤
      κ.M1 * (PT.tiling.P i).q := by
    apply max_le hgq
    nlinarith [(show (0 : ℝ) ≤ (PT.tiling.P i).q by positivity), hκ.M1_big.1]
  have hq : κ.Q0 ≤ ((PT.tiling.P i).q : ℝ) := by
    have hth : κ.M1 * κ.Q0 ≤
        max ((PT.tiling.P i).g : ℝ) ((PT.tiling.P i).q : ℝ) := by
      simpa only [Nat.cast_max] using hthreshold
    nlinarith [hth.trans hmax]
  apply hT.2
  apply le_trans (Real.rpow_le_rpow (Q0_pos hκ).le hq (Nat.cast_nonneg _))
  simpa [hm] using hhl

theorem fresh_factorization (D : LateData hPT)
    (q : ℕ) (odd : Fin q → Pos T k) (f : Fin q → Fin (T.S.N k) → ℝ) :
    D.freshQueryIntegral q odd f =
      ∏ C ∈ (Finset.univ.filter fun C => ∃ a, D.geom.cellOf (odd a) = C),
        (D.cellPoolLaw C).E (fun P => if D.fresh.typical C P then
          (D.fresh.fresh C P).E (fun s =>
            ∏ a : {a : Fin q // D.geom.cellOf (odd a) = C},
              f a.1 (D.fresh.label C s (odd a.1))) else 0) := by
  classical
  let c := fun a => D.geom.cellOf (odd a)
  let S := Finset.univ.filter fun C => ∃ a, c a = C
  let test (C : D.geom.Cell) (s : D.fresh.State C) :=
    ∏ a : {a : Fin q // c a = C}, f a.1 (D.fresh.label C s (odd a.1))
  let localTest (C : D.geom.Cell) (P : D.fresh.Pool C) :=
    if D.fresh.typical C P then (D.fresh.fresh C P).E (test C) else 0
  let d := D.encoding.pools_nonempty.choose
  let poolLaw (C : D.geom.Cell) := FinLaw.uniform Finset.univ
    (show (Finset.univ : Finset (D.fresh.Pool C)).Nonempty from ⟨d C, Finset.mem_univ _⟩)
  have hiid : D.encoding.iidLaw = FinLaw.pi poolLaw := by
    exact uniform_pi d
  have hstate (pools : ∀ C, D.fresh.Pool C) :
      (FinLaw.pi fun C => D.fresh.fresh C (pools C)).E
        (fun s => ∏ a, f a (D.earlyLabel s (odd a))) =
        ∏ C ∈ S, (D.fresh.fresh C (pools C)).E (test C) := by
    have hpoint (s : Config D.fresh) :
        (∏ a, f a (D.earlyLabel s (odd a))) = ∏ C ∈ S, test C (s C) := by
      dsimp only [test, LateData.earlyLabel]
      have hEq : (∏ C ∈ S, ∏ a : {a : Fin q // c a = C},
        f a.1 (D.fresh.label C (s C) (odd a.1))) =
      ∏ C ∈ S, ∏ a : {a : Fin q // c a = C},
        f a.1 (D.fresh.label (c a.1) (s (c a.1)) (odd a.1)) := by
        apply Finset.prod_congr rfl
        intro C _
        apply Finset.prod_congr rfl
        intro a _
        rw [a.2]
      rw [hEq]
      simpa only [S, c] using (prod_consulted c
        (fun a => f a (D.fresh.label (c a) (s (c a)) (odd a)))).symm
    calc
      _ = (FinLaw.pi fun C => D.fresh.fresh C (pools C)).E
          (fun s => ∏ C ∈ S, test C (s C)) := by simp_rw [hpoint]
      _ = _ := pi_consulted (fun C => D.fresh.fresh C (pools C)) S test
  have hmargin (C : D.geom.Cell) : (D.cellPoolLaw C).E (localTest C) =
      (poolLaw C).E (localTest C) := by
    rw [LateData.cellPoolLaw, S16.Lane_q_s16_comp2.map_expect, hiid]
    exact pi_coordinate poolLaw d C (localTest C)
  have ht (pools : ∀ C, D.fresh.Pool C) :
      (if ∀ a, D.fresh.typical (c a) (pools (c a)) then
        ∏ C ∈ S, (D.fresh.fresh C (pools C)).E (test C) else 0) =
        ∏ C ∈ S, localTest C (pools C) := by
    have h := prod_typical c S (fun C => by simp [S])
      (fun C => D.fresh.typical C (pools C))
      (fun C => (D.fresh.fresh C (pools C)).E (test C))
    by_cases ha : ∀ a, D.fresh.typical (c a) (pools (c a))
    · simpa only [localTest, if_pos ha] using h
    · simpa only [localTest, if_neg ha] using h
  calc
    D.freshQueryIntegral q odd f = D.encoding.iidLaw.E
        (fun pools => ∏ C ∈ S, localTest C (pools C)) := by
      unfold LateData.freshQueryIntegral
      apply congrArg
      funext pools
      rw [hstate]
      exact ht pools
    _ = ∏ C ∈ S, (poolLaw C).E (localTest C) := by
      rw [hiid]
      exact pi_consulted poolLaw S localTest
    _ = _ := by
      apply Finset.prod_congr rfl
      intro C _
      exact (hmargin C).symm

theorem prod_fibres {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (c : A → I) (S : Finset I) (hS : ∀ a, c a ∈ S) (b : A → ℝ) :
    (∏ C ∈ S, ∏ a : {a // c a = C}, b a.1) = ∏ a, b a := by
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := S)
    (fun a _ => hS a) b]
  apply Finset.prod_congr rfl
  intro C _
  exact (Finset.prod_subtype (Finset.univ.filter fun a => c a = C)
    (fun _ => by simp) b).symm

theorem fibre_bounds {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (c : A → I) (S : Finset I) (hS : ∀ a, c a ∈ S)
    (L : I → ℝ) (b : A → ℝ) (r : ℝ)
    (hL : ∀ C, 0 ≤ L C)
    (hB : ∀ C, L C ≤ Real.exp (r * Fintype.card {a // c a = C}) *
      ∏ a : {a // c a = C}, b a.1) :
    (∏ C ∈ S, L C) ≤
      Real.exp (r * Fintype.card A) * ∏ a, b a := by
  have hc : ∑ C ∈ S, Fintype.card {a // c a = C} = Fintype.card A := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset A)) (t := S) (f := c)
      (fun a _ => hS a)
    simpa only [Finset.card_univ, Fintype.card_subtype] using h.symm
  have hcR : (∑ C ∈ S, (Fintype.card {a // c a = C} : ℝ)) =
      (Fintype.card A : ℝ) := by exact_mod_cast hc
  calc
    (∏ C ∈ S, L C) ≤
        ∏ C ∈ S, Real.exp (r * Fintype.card {a // c a = C}) *
          ∏ a : {a // c a = C}, b a.1 := by
      apply Finset.prod_le_prod₀
      · intro C _; exact hL C
      · intro C _; exact hB C
    _ = (∏ C ∈ S, Real.exp (r * Fintype.card {a // c a = C})) *
        ∏ C ∈ S, ∏ a : {a // c a = C}, b a.1 := Finset.prod_mul_distrib
    _ = Real.exp (r * Fintype.card A) * ∏ a, b a := by
      rw [prod_fibres c S hS b, ← Real.exp_sum, ← Finset.mul_sum]
      rw [hcR]

end HypercubeRamsey.S18.Lane_sol_d18l_cal
