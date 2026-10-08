import HypercubeRamsey.S18.ReplayScope_sol_s18_3a_perm
import HypercubeRamsey.S18.HorizonPool_sol_s18_n5
import HypercubeRamsey.S16.Geometry_sol_s16_poolcmp

namespace HypercubeRamsey.Lane_sol_s18_3a_perm
open Classical Filter
open scoped BigOperators
open S18.Lane_sol_s18_n5

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid}

/-- A single prescribed slot has the same mass under the two physical pool laws. -/
theorem pool_pin_mass_equal (D : S18.LateData hPT) (p : S18.SlotPin D) :
    (∑ P ∈ Finset.univ.filter (fun P : ∀ C, D.fresh.Pool C => P p.1 p.2.1 = p.2.2),
      D.encoding.poolLaw.w P) =
    ∑ P ∈ Finset.univ.filter (fun P : ∀ C, D.fresh.Pool C => P p.1 p.2.1 = p.2.2),
      D.encoding.iidLaw.w P := by
  exact Lane_sol_s16_poolcmp.pin_mass_equal D.geom D.encoding.pools_nonempty p.1 p.2.1 p.2.2

/-- The patch costs multiply for the pin-gated test. Equal pin masses
then preserve the same cost after conditioning, including zero-mass fallback. -/
theorem scoped_pinned_pool_comparison (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (pin : Option (S18.SlotPin D))
    (hpin : ∀ p, pin = some p → p.1 ∈ region)
    (hsize : ∀ i, ((scopedPatchSlots D region i).card : ℝ) ≤
      Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10))
    (hroom : ∀ i, 2 * (((scopedPatchSlots D region i).card : ℝ) + 1) ^ 2 ≤
      Fintype.card (Bin PT.tiling i))
    (hcost : (∏ i : Fin PT.tiling.m,
      (1 + ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
        Fintype.card (Bin PT.tiling i))) ≤ 2)
    (f : (∀ C, D.fresh.Pool C) → ℝ) (hf : ∀ P, 0 ≤ f P)
    (hlocal : ∀ P Q, (∀ C ∈ region, P C = Q C) → f P = f Q) :
    (poolPinnedLaw D D.encoding.poolLaw pin).E f ≤
      2 * (poolPinnedLaw D D.encoding.iidLaw pin).E f := by
  cases pin with
  | none => exact scoped_pool_comparison D region hsize hroom hcost f hf hlocal
  | some p =>
    let A := Finset.univ.filter (fun P : ∀ C, D.fresh.Pool C => P p.1 p.2.1 = p.2.2)
    have hm : (∑ P ∈ A, D.encoding.poolLaw.w P) =
        ∑ P ∈ A, D.encoding.iidLaw.w P := pool_pin_mass_equal D p
    by_cases hP : 0 < ∑ P ∈ A, D.encoding.poolLaw.w P
    · have hQ : 0 < ∑ P ∈ A, D.encoding.iidLaw.w P := hm ▸ hP
      change (if h : 0 < ∑ P ∈ A, D.encoding.poolLaw.w P then
        FinLaw.cond D.encoding.poolLaw A h else D.encoding.poolLaw).E f ≤
          2 * (if h : 0 < ∑ P ∈ A, D.encoding.iidLaw.w P then
            FinLaw.cond D.encoding.iidLaw A h else D.encoding.iidLaw).E f
      rw [dif_pos hP, dif_pos hQ, Lane_sol_s16_poolcmp.cond_E,
        Lane_sol_s16_poolcmp.cond_E]
      let g := fun P : ∀ C, D.fresh.Pool C => if P ∈ A then f P else 0
      have hg : ∀ P, 0 ≤ g P := by intro P; dsimp [g]; split_ifs <;> simp [hf]
      have hglocal : ∀ P Q, (∀ C ∈ region, P C = Q C) → g P = g Q := by
        intro P Q hpq
        have hv := congrFun (hpq p.1 (hpin p rfl)) p.2.1
        have he := hlocal P Q hpq
        simp only [g, A, Finset.mem_filter, Finset.mem_univ, true_and, hv, he]
      have hc := scoped_pool_comparison D region hsize hroom hcost g hg hglocal
      rw [hm]
      simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc hQ.le
    · have hQ : ¬0 < ∑ P ∈ A, D.encoding.iidLaw.w P := by rwa [hm] at hP
      change (if h : 0 < ∑ P ∈ A, D.encoding.poolLaw.w P then
        FinLaw.cond D.encoding.poolLaw A h else D.encoding.poolLaw).E f ≤
          2 * (if h : 0 < ∑ P ∈ A, D.encoding.iidLaw.w P then
            FinLaw.cond D.encoding.iidLaw A h else D.encoding.iidLaw).E f
      rw [dif_neg hP, dif_neg hQ]
      exact scoped_pool_comparison D region hsize hroom hcost f hf hlocal

noncomputable def pinnedReplaySeed (D : S18.LateData hPT) (F : S18.LateEvent D)
    (pin : Option (S18.SlotPin D)) : Finset D.geom.Cell :=
  let seed := (cubeBall F.2.2.1.1 (10 * D.geom.r)).biUnion D.directCells
  match pin with
  | none => seed
  | some p => insert p.1 seed

private theorem expandCells_mono (D : S18.LateData hPT)
    {A B : Finset D.geom.Cell} (h : A ⊆ B) : D.expandCells A ⊆ D.expandCells B := by
  have hseed : A.biUnion D.encoding.events.incidentEvents ⊆
      B.biUnion D.encoding.events.incidentEvents := Finset.biUnion_subset_biUnion_of_subset_left _ h
  have hball : ∀ t, D.encoding.events.graphBall (A.biUnion D.encoding.events.incidentEvents) t ⊆
      D.encoding.events.graphBall (B.biUnion D.encoding.events.incidentEvents) t := by
    intro t
    induction t with
    | zero => exact hseed
    | succ t ih =>
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_union.mpr (Or.inl (ih hv))
      · obtain ⟨u, hu, hadj⟩ := (Finset.mem_filter.mp hv).2
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, u, ih hu, hadj⟩))
  exact Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ (hball _))

theorem lateRegion_subset_pinnedReplayRegion (D : S18.LateData hPT) (F : S18.LateEvent D)
    (pin : Option (S18.SlotPin D)) :
    D.lateRegion F ⊆ D.expandCells (pinnedReplaySeed D F pin) := by
  apply expandCells_mono D
  cases pin with
  | none => exact Finset.Subset.refl _
  | some p => exact Finset.subset_insert _ _

theorem pin_mem_pinnedReplayRegion (D : S18.LateData hPT) (F : S18.LateEvent D)
    (p : S18.SlotPin D) : p.1 ∈ D.expandCells (pinnedReplaySeed D F (some p)) :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self _ _))

private theorem pinnedReplaySeed_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (F : S18.LateEvent D) (pin : Option (S18.SlotPin D)) :
    (pinnedReplaySeed D F pin).card ≤ T.S.n k ^ (20 * D.geom.r + 3) := by
  let seed := (cubeBall F.2.2.1.1 (10 * D.geom.r)).biUnion D.directCells
  have hdirect : ∀ v, (D.directCells v).card ≤ T.S.n k + 1 := by
    intro v
    simpa only [hD.scope_eq] using Lane_sol_s18_n4.eventScope_card_le D hD v
  have hn2 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  have hs : seed.card ≤ T.S.n k ^ (20 * D.geom.r + 2) := by
    calc
      _ ≤ (cubeBall F.2.2.1.1 (10 * D.geom.r)).card * (T.S.n k + 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun w _ => hdirect w)
      _ ≤ (T.S.n k + 1) ^ (10 * D.geom.r) * (T.S.n k + 1) :=
        Nat.mul_le_mul_right _ (Lane_sol_s18_4b.cubeBall_card _ _)
      _ ≤ (T.S.n k ^ 2) ^ (10 * D.geom.r) * T.S.n k ^ 2 :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hn2 _) hn2
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1 <;> omega
  have hp : (pinnedReplaySeed D F pin).card ≤ seed.card + 1 := by
    cases pin with
    | none => exact Nat.le_add_right _ _
    | some p => exact Finset.card_insert_le _ _
  have hx : 1 ≤ T.S.n k ^ (20 * D.geom.r + 2) := Nat.one_le_pow _ _ (by omega)
  calc
    _ ≤ T.S.n k ^ (20 * D.geom.r + 2) + 1 := hp.trans (Nat.add_le_add_right hs 1)
    _ ≤ T.S.n k ^ (20 * D.geom.r + 2) * T.S.n k := by nlinarith
    _ = _ := by
      rw [show 20 * D.geom.r + 3 = (20 * D.geom.r + 2) + 1 by omega]
      exact (pow_succ _ _).symm

/-- Adding the global pin to the 10r replay seed still fits the logarithmic
seed budget, uniformly in the event, tiling, and pin. -/
theorem pinnedReplaySeed_eventually (κ : CConsts) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → ∀ (F : S18.LateEvent D) (pin : Option (S18.SlotPin D)),
      ((pinnedReplaySeed D F pin).card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) := by
  let C : ℝ := 2 * κ.A0 / Real.log 2
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
    T.S.n_tendsto
  filter_upwards [T.S.n_tendsto.eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp hnR).eventually_ge_atTop (max 1 (20 * C + 3))] with k hn hl
  intro PT hPT D hD F pin
  let y := Real.log (T.S.n k : ℝ)
  have hy : 1 ≤ y := (le_max_left _ _).trans hl
  have hyC : 20 * C + 3 ≤ y := (le_max_right _ _).trans hl
  have hnPos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (show 0 < T.S.n k by omega)
  have hr : (D.geom.r : ℝ) ≤ C * y := by
    dsimp [C, y]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr D.l16_valid.r_upper
  have he : ((20 * D.geom.r + 3 : ℕ) : ℝ) ≤ y ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hyC (by linarith : 0 ≤ y)
    push_cast
    nlinarith
  have hpower : (T.S.n k : ℝ) ^ (20 * D.geom.r + 3) ≤ Real.exp (y ^ 3) := by
    rw [← Real.exp_log hnPos, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right he (by linarith : 0 ≤ y)
    nlinarith
  have hs : ((pinnedReplaySeed D F pin).card : ℝ) ≤ (T.S.n k : ℝ) ^ (20 * D.geom.r + 3) := by
    exact_mod_cast pinnedReplaySeed_card D hD hn F pin
  exact hs.trans hpower

/-- Every patch has room for the augmented horizon, and the product of
its slot comparison costs is eventually at most two. -/
theorem pinnedReplay_pool_cost_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → ∀ (F : S18.LateEvent D) (pin : Option (S18.SlotPin D)),
      let region := D.expandCells (pinnedReplaySeed D F pin)
      (∀ i, ((scopedPatchSlots D region i).card : ℝ) ≤
        Real.exp (Real.rpow (Real.log (T.S.n k : ℝ)) 10)) ∧
      (∀ i, 2 * (((scopedPatchSlots D region i).card : ℝ) + 1) ^ 2 ≤
        Fintype.card (Bin PT.tiling i)) ∧
      (∏ i : Fin PT.tiling.m,
        (1 + ((scopedPatchSlots D region i).card : ℝ) ^ 2 /
          Fintype.card (Bin PT.tiling i))) ≤ 2 := by
  filter_upwards [pinnedReplaySeed_eventually κ T, horizon_pool_budget_eventually hκ T] with k hseed hbudget
  intro PT hPT D hD F pin
  exact hbudget D hD (pinnedReplaySeed D F pin) (hseed D hD F pin)

/-- The enlarged deterministic horizon pays all patchwise comparison costs,
including the global pin, with one uniform factor of two. -/
theorem pinnedReplay_pool_comparison_eventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec → ∀ (F : S18.LateEvent D) (pin : Option (S18.SlotPin D)),
      ∀ f : (∀ C, D.fresh.Pool C) → ℝ, (∀ P, 0 ≤ f P) →
      (∀ P Q, (∀ C ∈ D.lateRegion F, P C = Q C) → f P = f Q) →
      (poolPinnedLaw D D.encoding.poolLaw pin).E f ≤
        2 * (poolPinnedLaw D D.encoding.iidLaw pin).E f := by
  filter_upwards [pinnedReplay_pool_cost_eventually hκ T] with k hbudget
  intro PT hPT D hD F pin f hf hlocal
  obtain ⟨hsize, hroom, hcost⟩ := hbudget D hD F pin
  refine scoped_pinned_pool_comparison D (D.expandCells (pinnedReplaySeed D F pin)) pin
    ?_ hsize hroom hcost f hf ?_
  · intro p hp
    subst pin
    exact pin_mem_pinnedReplayRegion D F p
  · intro P Q hpq
    apply hlocal P Q
    intro C hC
    exact hpq C (lateRegion_subset_pinnedReplayRegion D F pin hC)

end HypercubeRamsey.Lane_sol_s18_3a_perm
