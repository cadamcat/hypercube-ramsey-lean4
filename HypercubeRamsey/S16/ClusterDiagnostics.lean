import HypercubeRamsey.S16.ProducersDefs
import HypercubeRamsey.S16.ClusterDiagnostics_q_s16_gate1
import HypercubeRamsey.S16.ClusterDiagnostics_q_s16_conc

/-! Cluster diagnostics proof nodes from the S16 pool diagnosis. -/

namespace HypercubeRamsey.S16.ClusterDiagnostics

open Classical
open scoped BigOperators
open Lane_sol_fix2_s16

/-- Fill the coordinates outside a finite scope from a fixed base point. -/
noncomputable def fillScope {J Bin : Type*} (I : Finset J) (base : J → Bin) (a : I → Bin) : J → Bin :=
  fun g => if h : g ∈ I then a ⟨g, h⟩ else base g

/-- Slot-expanded empirical integral of `f` over the scope `I`, with weights
`B * P j`; the coordinates outside `I` are frozen at `base`. -/
noncomputable def scopedEmpirical {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (pool : Slot → Bin) : ℝ :=
  Lane_sol_s16_prod1.empirical_statistic
    (Lane_sol_s16_prod1.empirical_weighted_kernel (fun j : I => P j.1) (Fintype.card Bin)
      (fun a => f (fillScope I base a))) pool

/-- C1. One-slot sensitivity (from `empirical_statistic_one_slot`).
TeX 16:235–249; estimated proof: 40 lines. -/
theorem scopedEmpirical_one_slot {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [Nonempty Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (A : ℝ) (hA : 1 ≤ A)
    (hcap : ∀ j b, (P j).w b ≤ A / Fintype.card Bin)
    (s : Slot) (x y : Slot → Bin) (hxy : ∀ t, t ≠ s → x t = y t) :
    |scopedEmpirical I P base f x - scopedEmpirical I P base f y| ≤
      (I.card : ℝ) * A ^ I.card / Fintype.card Slot := by
  classical
  let P' : I → FinLaw Bin := fun j => P j.1
  let f' : (I → Bin) → ℝ := fun a => f (fillScope I base a)
  let F : (I → Bin) → ℝ :=
    Lane_sol_s16_prod1.empirical_weighted_kernel P' (Fintype.card Bin) f'
  have hB : (0 : ℝ) < Fintype.card Bin := by positivity
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hF : ∀ a, 0 ≤ F a ∧ F a ≤ A ^ Fintype.card I := by
    simpa only [F, P', f'] using
      (Lane_sol_s16_prod1.empirical_weighted_kernel_range
        P' (Fintype.card Bin) A hB hA0
        (by intro j b; exact hcap j.1 b)
        f' (by intro a; exact hf (fillScope I base a)))
  simpa [scopedEmpirical, F, P', f'] using
    (Lane_sol_s16_prod1.empirical_statistic_one_slot
      F (A ^ Fintype.card I) (pow_nonneg hA0 _) hF s x y hxy)

/-- C2. Mean under iid uniform slots (from `empirical_statistic_mean`,
`empirical_weighted_kernel_range` and `empirical_weighted_kernel_integral`).
TeX 16:235–249; estimated proof: 50 lines. -/
theorem scopedEmpirical_mean {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [DecidableEq Bin]
    [Nonempty Bin]
    (I : Finset J) (P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (A : ℝ) (hA : 1 ≤ A)
    (hcap : ∀ j b, (P j).w b ≤ A / Fintype.card Bin) :
    (FinLaw.pi (fun _ : Slot => FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E
        (scopedEmpirical I P base f) ≤
      (FinLaw.pi (fun j : I => P j.1)).E (fun a => f (fillScope I base a)) +
        A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot) := by
  classical
  let P' : I → FinLaw Bin := fun j => P j.1
  let f' : (I → Bin) → ℝ := fun a => f (fillScope I base a)
  let F : (I → Bin) → ℝ :=
    Lane_sol_s16_prod1.empirical_weighted_kernel P' (Fintype.card Bin) f'
  have hB : (0 : ℝ) < Fintype.card Bin := by positivity
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hF : ∀ a, 0 ≤ F a ∧ F a ≤ A ^ Fintype.card I := by
    simpa only [F, P', f'] using
      (Lane_sol_s16_prod1.empirical_weighted_kernel_range
        P' (Fintype.card Bin) A hB hA0
        (by intro j b; exact hcap j.1 b)
        f' (by intro a; exact hf (fillScope I base a)))
  have hmean := Lane_sol_s16_prod1.empirical_statistic_mean
    (Index := I) (Slot := Slot) (Bin := Bin)
    F (FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)
    (A ^ Fintype.card I) (pow_nonneg hA0 _) hF
  change
    (FinLaw.pi (fun _ : Slot =>
      FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E
        (Lane_sol_s16_prod1.empirical_statistic F) ≤
      (FinLaw.pi P').E f' +
        A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot)
  calc
    _ ≤ (FinLaw.pi (fun _ : I =>
          FinLaw.uniform (Finset.univ : Finset Bin) Finset.univ_nonempty)).E F +
          A ^ Fintype.card I * ((Fintype.card I : ℝ) ^ 2 / Fintype.card Slot) := by
      exact hmean
    _ = (FinLaw.pi P').E f' +
          A ^ I.card * ((I.card : ℝ) ^ 2 / Fintype.card Slot) := by
      rw [Lane_sol_s16_prod1.empirical_weighted_kernel_integral P' f']
      simp only [Fintype.card_coe]

/-- C3. The pool-restricted integral is bounded by the slot expansion, on
every pool (repeated images only enlarge the right side).
TeX 16:235–249; estimated proof: 150 lines. -/
theorem scopedEmpirical_restricted {J Slot Bin : Type*} [DecidableEq J]
    [Fintype Slot] [DecidableEq Slot] [Nonempty Slot] [Fintype Bin] [DecidableEq Bin]
    (I : Finset J) (Q P : J → FinLaw Bin) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ a, 0 ≤ f a) (pool : Slot → Bin)
    (hmass : ∀ j ∈ I, 0 < ∑ b ∈ Finset.univ.image pool, (Q j).w b)
    (hP : ∀ j ∈ I, ∀ b, (P j).w b =
      (if b ∈ Finset.univ.image pool then (Q j).w b else 0) /
        ∑ b' ∈ Finset.univ.image pool, (Q j).w b') :
    (FinLaw.pi (fun j : I => P j.1)).E (fun a => f (fillScope I base a)) *
        ∏ j ∈ I, ((Fintype.card Bin : ℝ) / Fintype.card Slot *
          ∑ b ∈ Finset.univ.image pool, (Q j).w b) ≤
      scopedEmpirical I Q base f pool := by
  sorry

/-- C4a. Marginalisation of a scope-local integrand.
TeX 16:235–245; estimated proof: 40 lines. -/
theorem pi_E_scope {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (base : J → Bin) (f : (J → Bin) → ℝ)
    (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi R).E f = (FinLaw.pi (fun j : I => R j.1)).E (fun a => f (fillScope I base a)) := by
  sorry

/-- C4b. The same with one coordinate of the scope pinned.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pi_E_scope_pin {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (g : J) (hg : g ∈ I) (b : Bin)
    (base : J → Bin) (hbase : base g = b) (f : (J → Bin) → ℝ)
    (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f =
      (FinLaw.pi (fun j : (I.erase g) => R j.1)).E
        (fun a => f (fillScope (I.erase g) base a)) := by
  sorry

/-- C4c. A pin outside the scope is invisible.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pi_E_pin_outside {J Bin : Type*} [Fintype J] [DecidableEq J] [Fintype Bin]
    [DecidableEq Bin] [Nonempty Bin]
    (R : J → FinLaw Bin) (I : Finset J) (g : J) (hg : g ∉ I) (b : Bin)
    (f : (J → Bin) → ℝ) (hf : ∀ x y, (∀ g ∈ I, x g = y g) → f x = f y) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin R g b)).E f = (FinLaw.pi R).E f := by
  sorry

/-- C4d. Injective reindexing commutes with a coordinate pin.
TeX 16:239–245; estimated proof: 40 lines. -/
theorem pi_coordinatePin_comp {I J O : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]
    (P : I → FinLaw O) (ι : J → I) (hι : Function.Injective ι) (j : J) (o : O)
    (F : (J → O) → ℝ) :
    (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P (ι j) o)).E (fun a => F (fun j' => a (ι j'))) =
      (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin (fun j' => P (ι j')) j o)).E F := by
  sorry

/-- C4e. `GroupBinProblem.pinnedFailure` as a pinned product integral.
TeX 16:228–245; estimated proof: 40 lines. -/
theorem pinned_ratio_eq {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (P : I → FinLaw O) (i : I) (o : O) (f : (I → O) → ℝ) :
    (FinLaw.pi P).E (fun a => if a i = o then f a else 0) /
        (FinLaw.pi P).pr (fun a => a i = o) =
      if (P i).w o = 0 then 0 else (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin P i o)).E f := by
  sorry

/-- C5. A slot pin moves an expectation by at most the one-slot sensitivity.
TeX 16:247–257; estimated proof: 80 lines. -/
theorem pinLaw_E_close {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0) (Φ : (Slot → Bin) → ℝ)
    (s : Slot) (b : Bin) (δ : ℝ)
    (hΦ : ∀ x y, (∀ t, t ≠ s → x t = y t) → |Φ x - Φ y| ≤ δ) :
    |(D.pinLaw s b).E Φ - D.poolLaw.E Φ| ≤ δ := by
  classical
  letI : Nonempty Bin := D.bins_nonempty
  let Ppin : Slot → FinLaw Bin := fun t =>
    if t = s then FinLaw.dirac b else D.iidSlotLaw t
  let Ψ : (Slot → Bin) → ℝ := fun x => Φ (Function.update x s b)
  have hreplace : (FinLaw.pi Ppin).E Φ = (FinLaw.pi Ppin).E Ψ := by
    unfold FinLaw.E
    apply Finset.sum_congr rfl
    intro x hx
    change (∏ t, (Ppin t).w (x t)) * Φ x =
      (∏ t, (Ppin t).w (x t)) * Φ (Function.update x s b)
    have hprod : (∏ t, (Ppin t).w (x t)) =
        (Ppin s).w (x s) * ∏ t ∈ Finset.univ.erase s, (Ppin t).w (x t) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ s)]
    rw [hprod]
    by_cases hxs : x s = b
    · have hupdate : Function.update x s b = x := by
        funext t
        by_cases ht : t = s <;> simp [ht, hxs]
      simp [hupdate]
    · have hzero : (Ppin s).w (x s) = 0 := by
        simp [Ppin, hxs, FinLaw.dirac]
      simp [hzero]
  have hlocal : ∀ x y, (∀ t, t ∈ Finset.univ.erase s → x t = y t) → Ψ x = Ψ y := by
    intro x y hxy
    change Φ (Function.update x s b) = Φ (Function.update y s b)
    congr 1
    funext t
    by_cases hts : t = s
    · subst t
      simp
    · have ht : t ∈ Finset.univ.erase s :=
        Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩
      have h := hxy t ht
      simp [Function.update, hts, h]
  have hsame : ∀ t, t ∈ Finset.univ.erase s → Ppin t = D.iidSlotLaw t := by
    intro t ht
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    simp [Ppin, hts]
  have hpin : (FinLaw.pi Ppin).E Ψ = (FinLaw.pi D.iidSlotLaw).E Ψ :=
    Lane_sol_s16_prod1.pi_E_local Ppin D.iidSlotLaw (Finset.univ.erase s) Ψ hlocal hsame
  have hdiff : (FinLaw.pi D.iidSlotLaw).E Ψ - (FinLaw.pi D.iidSlotLaw).E Φ =
      (FinLaw.pi D.iidSlotLaw).E (fun x => Ψ x - Φ x) := by
    unfold FinLaw.E
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  change |(FinLaw.pi Ppin).E Φ - (FinLaw.pi D.iidSlotLaw).E Φ| ≤ δ
  rw [hreplace, hpin, hdiff]
  have hδ : 0 ≤ δ := by
    let x : Slot → Bin := fun _ => Classical.choice D.bins_nonempty
    have h := hΦ x x (by intro t ht; rfl)
    simpa using h
  have hpoint : ∀ x, |Ψ x - Φ x| ≤ δ := by
    intro x
    exact hΦ (Function.update x s b) x (by
      intro t ht
      simp [Function.update, ht])
  unfold FinLaw.E
  calc
    |∑ x, (FinLaw.pi D.iidSlotLaw).w x * (Ψ x - Φ x)| ≤
        ∑ x, |(FinLaw.pi D.iidSlotLaw).w x * (Ψ x - Φ x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, (FinLaw.pi D.iidSlotLaw).w x * |Ψ x - Φ x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg ((FinLaw.pi D.iidSlotLaw).nonneg x)]
    _ ≤ ∑ x, (FinLaw.pi D.iidSlotLaw).w x * δ :=
      Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hpoint x) ((FinLaw.pi D.iidSlotLaw).nonneg x)
    _ = δ := by rw [← Finset.sum_mul, (FinLaw.pi D.iidSlotLaw).sum_one, one_mul]

/-- C6. Per-check facts assemble the concentration record (mixed families).
TeX 16:247–257; estimated proof: 80 lines. -/
theorem pool_concentration_of_checks {Slot Bin Hist Check : Type*}
    [Fintype Slot] [DecidableEq Slot] [Fintype Bin] [DecidableEq Bin]
    [Fintype Hist] [Fintype Check] {n : ℕ} {c0 : ℝ}
    (D : CellPoolDiagnostics Slot Bin Hist Check n c0)
    (hn : 2 ≤ n) (hc0 : 0 < c0) (hslots : 0 < Fintype.card Slot)
    (heps : 0 < D.ε ∧ D.ε ≤ 1) (htol : ∀ c, 0 < D.tolerance c)
    (sens : Check → ℝ) (hsens : ∀ c, 0 < sens c)
    (hone : ∀ c s x y, (∀ t, t ≠ s → x t = y t) →
      |D.normalizer x c - D.normalizer y c| ≤ sens c)
    (hmean : ∀ c, |D.poolLaw.E (D.normalizer · c) - D.center c| + sens c ≤ D.tolerance c / 2)
    (hvar : ∀ c, (n : ℝ) ^ c0 + Real.log (8 * max 1 (Fintype.card Check : ℝ)) ≤
      2 * (D.tolerance c / 2) ^ 2 / ((Fintype.card Slot : ℝ) * sens c ^ 2))
    (hcollision : (Fintype.card Slot : ℝ) ^ 2 / Fintype.card Bin ≤
      Real.exp (-(n : ℝ) ^ c0) / 4) :
    Nonempty (PoolConcentrationHypotheses D) := by
  classical
  have hslotsReal : 0 < (Fintype.card Slot : ℝ) := by exact_mod_cast hslots
  refine ⟨{
    n_large := hn
    exponent_pos := hc0
    slots_pos := hslots
    epsilon_pos := heps
    tolerance_pos := htol
    sensitivity := fun c _ => sens c
    sensitivity_nonneg := fun c _ => (hsens c).le
    mean_close := ?_
    pinned_mean_close := ?_
    one_slot_change := ?_
    variance_budget := ?_
    collision_budget := hcollision }⟩
  · intro c
    have h := hmean c
    have hs : 0 ≤ sens c := (hsens c).le
    linarith
  · intro s b c
    have hpin := pinLaw_E_close D (D.normalizer · c) s b (sens c) (hone c s)
    have h := hmean c
    have hsum : sens c + |D.poolLaw.E (D.normalizer · c) - D.center c| ≤
        D.tolerance c / 2 := by linarith
    calc
      |(D.pinLaw s b).E (D.normalizer · c) - D.center c| ≤
          |(D.pinLaw s b).E (D.normalizer · c) - D.poolLaw.E (D.normalizer · c)| +
            |D.poolLaw.E (D.normalizer · c) - D.center c| :=
        abs_sub_le _ _ _
      _ ≤ D.tolerance c / 2 := by
        exact (add_le_add hpin (le_refl _)).trans hsum
  · exact hone
  · intro c
    have hsum : (∑ s : Slot, (fun _ : Slot => sens c) s ^ 2) =
        (Fintype.card Slot : ℝ) * sens c ^ 2 := by simp
    rw [hsum]
    exact Or.inr ⟨mul_pos hslotsReal (sq_pos_of_pos (hsens c)), hvar c⟩

/-- C7. Numerical room for star/pin checks: sensitivity, variance budget, cover.
TeX 16:247–257; estimated proof: 150 lines. -/
theorem cluster_star_budget_room : ∃ n₀ : ℕ, ∀ (n h : ℕ) (L ε Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → h ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L →
    Real.rpow (n : ℝ) (-1) ≤ ε → ε ≤ 1 / 10 ^ 6 →
    Checks ≤ Real.exp (3 * (n : ℝ) ^ (1.01 : ℝ)) →
    ((h : ℝ) + 1) * n / L ≤ Real.rpow ε (1 / 4 : ℝ) / 8 / 2 ∧
    Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      2 * (Real.rpow ε (1 / 4 : ℝ) / 8 / 2) ^ 2 / (L * (((h : ℝ) + 1) * n / L) ^ 2) ∧
    2 * Real.sqrt ε + (n : ℝ) * (h : ℝ) ^ 2 / L + Real.rpow ε (1 / 4 : ℝ) / 8 ≤
      (1 - Real.rpow (n : ℝ) (-4)) ^ h * Real.rpow ε (1 / 4 : ℝ) := by
  refine ⟨2, ?_⟩
  intro n h L ε Checks hn hn2 hh hL hεlower hepsSmall hchecks
  let x : ℝ := n
  let τ : ℝ := Real.rpow ε (1 / 4 : ℝ)
  let σ : ℝ := ((h : ℝ) + 1) * x / L
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hhCast : (h : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hh
  have hPlus : (h : ℝ) + 1 ≤ 2 * x := by linarith
  have hρ1 : Real.rpow x (-1) = 1 / x := by
    rw [Real.rpow_eq_pow, Real.rpow_neg, Real.rpow_one, one_div] <;> exact hx.le
  have hρ4 : Real.rpow x (-4) = 1 / x ^ (4 : ℕ) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div] <;> exact hx.le
  have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hx _) hεlower
  have hεle1 : ε ≤ 1 := by linarith
  have hεlower' : 1 / x ≤ ε := by
    calc
      1 / x = Real.rpow x (-1) := hρ1.symm
      _ ≤ ε := hεlower
  have hετ : ε ≤ τ := by
    calc
      ε = Real.rpow ε 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow ε (1 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hεpos hεle1
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
      _ = τ := rfl
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hεpos _
  have hτlower : 1 / x ≤ τ := hεlower'.trans hετ
  have hpow101 : Real.rpow x (1.01 : ℝ) ≤ x ^ (2 : ℕ) := by
    simpa only [Real.rpow_eq_pow, Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1.01 : ℝ) ≤ 2)
  have hmax : max 1 Checks ≤ Real.exp (3 * Real.rpow x (1.01 : ℝ)) := by
    refine max_le ?_ hchecks
    exact Real.one_le_exp_iff.mpr
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hx.le _))
  have hlog8 : Real.log 8 ≤ 8 := by
    have hhlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hlog : Real.log (8 * max 1 Checks) ≤ 8 + 3 * x ^ (2 : ℕ) := by
    calc
      _ ≤ Real.log (8 * Real.exp (3 * Real.rpow x (1.01 : ℝ))) :=
        Real.log_le_log (by positivity)
          (mul_le_mul_of_nonneg_left hmax (by norm_num))
      _ = Real.log 8 + 3 * Real.rpow x (1.01 : ℝ) := by
        rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
          (Real.exp_pos _).ne', Real.log_exp]
      _ ≤ 8 + 3 * x ^ (2 : ℕ) := by nlinarith [hlog8, hpow101]
  have hroot : Real.rpow x (1 / 2 : ℝ) ≤ x := by
    simpa only [Real.rpow_eq_pow, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hx196 : (32 : ℝ) ≤ x ^ (196 : ℕ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ x ^ (5 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (196 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hx195 : (4 : ℝ) ≤ x ^ (195 : ℕ) := by
    calc
      4 = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ x ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (195 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hσbound : σ ≤ 2 / x ^ (197 : ℕ) := by
    calc
      σ = ((h : ℝ) + 1) * x / L := by rfl
      _ ≤ 2 * x ^ (2 : ℕ) / L := by
        apply div_le_div_of_nonneg_right _ hLp.le
        have hh := mul_le_mul_of_nonneg_right hPlus hx.le
        nlinarith [hh]
      _ ≤ 2 * x ^ (2 : ℕ) / x ^ (199 : ℕ) := by
        apply (div_le_div_iff₀ hLp (pow_pos hx _)).mpr
        exact mul_le_mul_of_nonneg_left hL (by positivity)
      _ = 2 / x ^ (197 : ℕ) := by field_simp [hx.ne']
  have hx197 : x ^ (197 : ℕ) = x ^ (196 : ℕ) * x := by
    rw [show (197 : ℕ) = 196 + 1 by norm_num, pow_succ]
  have h32x : 32 * x ≤ x ^ (197 : ℕ) := by
    rw [hx197]
    exact mul_le_mul_of_nonneg_right hx196 hx.le
  have hσsmall : σ ≤ 1 / (16 * x) := by
    calc
      σ ≤ 2 / x ^ (197 : ℕ) := hσbound
      _ ≤ 1 / (16 * x) := by
        apply (div_le_div_iff₀ (pow_pos hx _) (mul_pos (by norm_num) hx)).mpr
        nlinarith [h32x]
  refine ⟨?_, ?_, ?_⟩
  · calc
      σ ≤ 1 / (16 * x) := hσsmall
      _ = (1 / x) / 16 := by ring
      _ ≤ τ / 16 := div_le_div_of_nonneg_right hτlower (by norm_num)
      _ = τ / 8 / 2 := by ring
  · have hτsq₀ : (Real.rpow ε (1 / 4 : ℝ)) ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hεpos.le]
      norm_num
    have hτsq : τ ^ 2 = Real.sqrt ε := by
      calc
        τ ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by simpa [τ] using hτsq₀
        _ = Real.sqrt ε := (Real.sqrt_eq_rpow _).symm
    have hεsqrt : ε ≤ Real.sqrt ε := by
      have hεsq : ε ^ 2 ≤ ε := by
        calc
          ε ^ 2 = ε * ε := by rw [pow_two]
          _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hεle1 hεpos.le
          _ = ε := by ring
      exact (Real.le_sqrt hεpos.le hεpos.le).mpr hεsq
    have hτsqLower : 1 / x ≤ τ ^ 2 := by rw [hτsq]; exact hεlower'.trans hεsqrt
    have hPlusSq : ((h : ℝ) + 1) ^ 2 ≤ 4 * x ^ (2 : ℕ) := by
      have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (h : ℝ) + 1) hPlus 2
      calc
        ((h : ℝ) + 1) ^ 2 ≤ (2 * x) ^ 2 := hpow
        _ = 4 * x ^ (2 : ℕ) := by ring
    have hden : 0 < 128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ) := by positivity
    have hdenUpper : 128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ) ≤
        512 * x ^ (4 : ℕ) := by
      have hh := mul_le_mul_of_nonneg_right hPlusSq (pow_nonneg hx.le (2 : ℕ))
      have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 128)
      calc
        _ = 128 * (((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := by ring
        _ ≤ 128 * ((4 * x ^ (2 : ℕ)) * x ^ (2 : ℕ)) := hh'
        _ = 512 * x ^ (4 : ℕ) := by ring
    have hx192 : (4096 : ℝ) ≤ x ^ (192 : ℕ) := by
      calc
        4096 = (2 : ℝ) ^ (12 : ℕ) := by norm_num
        _ ≤ x ^ (12 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
        _ ≤ x ^ (192 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
    have hx194 : x ^ (194 : ℕ) = x ^ (192 : ℕ) * x ^ (2 : ℕ) := by
      rw [← pow_add]
    have hx198 : x ^ (198 : ℕ) = x ^ (194 : ℕ) * x ^ (4 : ℕ) := by
      rw [← pow_add]
    have hnumLower : x ^ (198 : ℕ) ≤ τ ^ 2 * L := by
      calc
        x ^ (198 : ℕ) = (1 / x) * x ^ (199 : ℕ) := by field_simp [hx.ne']
        _ ≤ τ ^ 2 * L := mul_le_mul hτsqLower hL (by positivity) (by positivity)
    have hbig : 8 * x ^ (2 : ℕ) ≤ x ^ (194 : ℕ) / 512 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 512)).mpr
      have hh := mul_le_mul_of_nonneg_right hx192 (pow_nonneg hx.le (2 : ℕ))
      calc
        8 * x ^ (2 : ℕ) * 512 = 4096 * x ^ (2 : ℕ) := by ring
        _ ≤ x ^ (192 : ℕ) * x ^ (2 : ℕ) := by nlinarith [hh]
        _ = x ^ (194 : ℕ) := by rw [hx194]
    have hbudgetRaw : x ^ (194 : ℕ) / 512 ≤ τ ^ 2 * L /
        (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 512) hden).mpr
      calc
        x ^ (194 : ℕ) * (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) ≤
            x ^ (194 : ℕ) * (512 * x ^ (4 : ℕ)) :=
          mul_le_mul_of_nonneg_left hdenUpper (by positivity)
        _ = 512 * x ^ (198 : ℕ) := by rw [hx198]; ring
        _ ≤ 512 * (τ ^ 2 * L) := mul_le_mul_of_nonneg_left hnumLower (by norm_num)
        _ = (τ ^ 2 * L) * 512 := by ring
    have hbudget : 8 * x ^ (2 : ℕ) ≤ τ ^ 2 * L /
        (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := hbig.trans hbudgetRaw
    have hvarEq : 2 * (τ / 8 / 2) ^ 2 / (L * σ ^ 2) =
        τ ^ 2 * L / (128 * ((h : ℝ) + 1) ^ 2 * x ^ (2 : ℕ)) := by
      dsimp [σ]
      field_simp [hLp.ne', hx.ne'] <;> ring
    have hleft : Real.rpow x (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
        8 * x ^ (2 : ℕ) := by
      calc
        _ ≤ x + (8 + 3 * x ^ (2 : ℕ)) := add_le_add hroot hlog
        _ = x + 8 + 3 * x ^ (2 : ℕ) := by ring
        _ ≤ 6 * x ^ (2 : ℕ) := by
          have hxle : x ≤ x ^ (2 : ℕ) := by
            calc
              x = x * 1 := by ring
              _ ≤ x * x := mul_le_mul_of_nonneg_left hx1 hx.le
              _ = x ^ (2 : ℕ) := by ring
          have hxSq4 : 4 ≤ x ^ (2 : ℕ) := by
            calc
              4 = (2 : ℝ) ^ (2 : ℕ) := by norm_num
              _ ≤ x ^ (2 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
          have h8 : 8 ≤ 2 * x ^ (2 : ℕ) := by
            calc
              8 = 2 * 4 := by norm_num
              _ ≤ 2 * x ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hxSq4 (by norm_num)
          calc
            x + 8 + 3 * x ^ (2 : ℕ) ≤
                x ^ (2 : ℕ) + 2 * x ^ (2 : ℕ) + 3 * x ^ (2 : ℕ) :=
              add_le_add (add_le_add hxle h8) le_rfl
            _ = 6 * x ^ (2 : ℕ) := by ring
        _ ≤ 8 * x ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8) (pow_nonneg hx.le (2 : ℕ))
    have hbudgetGoal : Real.rpow x (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
        2 * (τ / 8 / 2) ^ 2 / (L * σ ^ 2) := by
      rw [hvarEq]
      exact hleft.trans hbudget
    exact hbudgetGoal
  · have hτcap : τ ≤ 1 / 10 := by
      have hεquarter : ε ≤ ((1 : ℝ) / 10) ^ (4 : ℕ) := by
        exact le_trans hepsSmall (by norm_num)
      calc
        τ = Real.rpow ε (1 / 4 : ℝ) := rfl
        _ ≤ Real.rpow (((1 : ℝ) / 10) ^ (4 : ℕ)) (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hεpos.le hεquarter (by norm_num)
        _ = 1 / 10 := by
          have hmul : Real.rpow (Real.rpow (1 / 10 : ℝ) 4) (1 / 4 : ℝ) =
              Real.rpow (1 / 10 : ℝ) (4 * (1 / 4 : ℝ)) :=
            (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (1 / 10)) 4 (1 / 4 : ℝ)).symm
          rw [show ((1 : ℝ) / 10) ^ (4 : ℕ) = Real.rpow (1 / 10 : ℝ) 4 by
            exact (Real.rpow_natCast _ _).symm, hmul]
          norm_num
    have hτsq : τ ^ 2 = Real.sqrt ε := by
      have hs : (Real.rpow ε (1 / 4 : ℝ)) ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hεpos.le]
        norm_num
      calc
        τ ^ 2 = Real.rpow ε (1 / 2 : ℝ) := by simpa [τ] using hs
        _ = Real.sqrt ε := (Real.sqrt_eq_rpow _).symm
    have hrootSmall : 2 * Real.sqrt ε ≤ τ / 5 := by
      rw [← hτsq]
      have hh := mul_le_mul_of_nonneg_left hτcap (by positivity : 0 ≤ 2 * τ)
      nlinarith [hτpos]
    have hLerr : 4 * x ^ (4 : ℕ) ≤ L := by
      calc
        4 * x ^ (4 : ℕ) ≤ x ^ (195 : ℕ) * x ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hx195 (pow_nonneg hx.le _)
        _ = x ^ (199 : ℕ) := by rw [← pow_add]
        _ ≤ L := hL
    have hhSq : (h : ℝ) ^ 2 ≤ x ^ (2 : ℕ) := by
      have hh' := mul_le_mul hhCast hhCast (by positivity) (by positivity)
      simpa only [pow_two] using hh'
    have herr : x * (h : ℝ) ^ 2 / L ≤ τ / 4 := by
      have hbase : x * (h : ℝ) ^ 2 / L ≤ 1 / (4 * x) := by
        calc
          _ ≤ x ^ (3 : ℕ) / L := by
            apply div_le_div_of_nonneg_right _ hLp.le
            have hh' := mul_le_mul_of_nonneg_left hhSq hx.le
            calc
              x * (h : ℝ) ^ 2 ≤ x * x ^ (2 : ℕ) := hh'
              _ = x ^ (3 : ℕ) := by ring
        _ ≤ 1 / (4 * x) := by
            apply (div_le_div_iff₀ hLp (mul_pos (by norm_num) hx)).mpr
            have hxpow : x ^ (3 : ℕ) * (4 * x) = 4 * x ^ (4 : ℕ) := by ring
            rw [hxpow]
            simpa only [one_mul] using hLerr
      calc
        x * (h : ℝ) ^ 2 / L ≤ 1 / (4 * x) := hbase
        _ = (1 / x) / 4 := by ring
        _ ≤ τ / 4 := div_le_div_of_nonneg_right hτlower (by norm_num)
    have hfactor : (7 / 8 : ℝ) ≤ (1 - Real.rpow x (-4)) ^ h := by
      let t : ℝ := 1 / x ^ (4 : ℕ)
      have ht0 : 0 ≤ t := by dsimp [t]; positivity
      have ht1 : t ≤ 1 := by
        dsimp [t]
        apply (div_le_iff₀ (pow_pos hx _)).mpr
        simpa only [one_mul] using (one_le_pow₀ hx1 : (1 : ℝ) ≤ x ^ (4 : ℕ))
      have hbern : ∀ m : ℕ, 0 ≤ t → t ≤ 1 →
          1 - (m : ℝ) * t ≤ (1 - t) ^ m := by
        intro m
        induction m with
        | zero => intro _ _; simp
        | succ m ih =>
            intro ht0 ht1
            have hpow : (1 - t) ^ m ≤ 1 :=
              pow_le_one₀ (sub_nonneg.mpr ht1) (sub_le_self 1 ht0)
            have hprod : t * (1 - t) ^ m ≤ t := by
              simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow ht0
            calc
              1 - ((m + 1 : ℕ) : ℝ) * t = (1 - (m : ℝ) * t) - t := by push_cast; ring
              _ ≤ (1 - t) ^ m - t := sub_le_sub_right (ih ht0 ht1) _
              _ ≤ (1 - t) ^ m - t * (1 - t) ^ m :=
                sub_le_sub_left hprod ((1 - t) ^ m)
              _ = (1 - t) ^ (m + 1) := by rw [pow_succ]; ring
      have hx3 : (8 : ℝ) ≤ x ^ (3 : ℕ) := by
        calc
          8 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
          _ ≤ x ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      have hrecip3 : 1 / x ^ (3 : ℕ) ≤ 1 / 8 := by
        apply (div_le_div_iff₀ (pow_pos hx _) (by norm_num)).mpr
        simpa using hx3
      have hxt : x * t = 1 / x ^ (3 : ℕ) := by
        dsimp [t]
        field_simp [hx.ne']
      have hhT : (h : ℝ) * t ≤ x * t := mul_le_mul_of_nonneg_right hhCast ht0
      have hber : 1 - (h : ℝ) * t ≤ (1 - t) ^ h := hbern h ht0 ht1
      calc
        (7 / 8 : ℝ) ≤ 1 - 1 / x ^ (3 : ℕ) := by linarith
        _ = 1 - x * t := by rw [hxt]
        _ ≤ 1 - (h : ℝ) * t := sub_le_sub_left hhT _
        _ ≤ (1 - t) ^ h := hber
        _ = (1 - Real.rpow x (-4)) ^ h := by
          dsimp [t]
          have hb : 1 - 1 / x ^ (4 : ℕ) = 1 - Real.rpow x (-4) := by rw [hρ4]
          exact congrArg (fun y : ℝ => y ^ h) hb
    have hrootQuarter : 2 * Real.sqrt ε ≤ τ / 4 := by
      have hfrac : τ / 5 ≤ τ / 4 := by
        apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr
        exact mul_le_mul_of_nonneg_left (by norm_num : (4 : ℝ) ≤ 5) hτpos.le
      exact hrootSmall.trans hfrac
    have hfracEighth : τ / 8 ≤ τ / 4 := by
      apply (div_le_div_iff₀ (by norm_num) (by norm_num)).mpr
      exact mul_le_mul_of_nonneg_left (by norm_num : (4 : ℝ) ≤ 8) hτpos.le
    have hcoverL : 2 * Real.sqrt ε + x * (h : ℝ) ^ 2 / L + τ / 8 ≤
        (7 / 8 : ℝ) * τ := by
      calc
        2 * Real.sqrt ε + x * (h : ℝ) ^ 2 / L + τ / 8 ≤ τ / 4 + τ / 4 + τ / 4 :=
          add_le_add (add_le_add hrootQuarter herr) hfracEighth
        _ = (3 / 4 : ℝ) * τ := by ring
        _ ≤ (7 / 8 : ℝ) * τ :=
          mul_le_mul_of_nonneg_right (by norm_num) hτpos.le
    have hcoverR : (7 / 8 : ℝ) * τ ≤
        (1 - Real.rpow x (-4)) ^ h * τ :=
      mul_le_mul_of_nonneg_right hfactor hτpos.le
    have hcover := hcoverL.trans hcoverR
    exact hcover

/-- C8. `cluster_normalizer_budget_room` with the total check count.
TeX 16:206–219,247–257; estimated proof: 100 lines. -/
theorem cluster_normalizer_budget_room3 : ∃ n₀ : ℕ, ∀ (n : ℕ) (L B Checks : ℝ),
    n₀ ≤ n → 2 ≤ n → 0 < B → (n : ℝ) ^ (199 : ℕ) ≤ L →
    L ^ 2 / B ≤ Real.exp (-Real.rpow (n : ℝ) (1 / 2 : ℝ)) / 4 →
    Checks ≤ Real.exp (3 * (n : ℝ) ^ (1.01 : ℝ)) →
    ((n : ℝ) * L ^ 2 / B + ((n : ℝ) + 1) / L ≤ Real.rpow (n : ℝ) (-4) / 2) ∧
    (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
      L * Real.rpow (n : ℝ) (-4) ^ 2 / (8 * (n : ℝ) ^ (2 : ℕ))) := by
  obtain ⟨n₀, hroom⟩ := Lane_sol_s16_prod1.logarithmic_room
    (1 / 2) 1 0 5 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨n₀, ?_⟩
  intro n L B Checks hn hn2 hB hL hcollision hchecks
  let x : ℝ := n
  have hx2 : (2 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hn2
  have hx : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hLp : 0 < L := lt_of_lt_of_le (pow_pos hx _) hL
  have hρ : Real.rpow x (-4) = 1 / x ^ (4 : ℕ) := by
    rw [Real.rpow_eq_pow, Real.rpow_neg,
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div] <;> exact hx.le
  have hsmall : Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ 1 / x ^ (5 : ℕ) := by
    have hr := hroom n hn
    simp only [one_mul, zero_add] at hr
    have he := Real.exp_le_exp.mpr (neg_le_neg hr)
    have he5 : Real.exp (5 * Real.log x) = x ^ (5 : ℕ) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hx] using Real.exp_nat_mul (Real.log x) 5
    change Real.exp (-Real.rpow x (1 / 2 : ℝ)) ≤ Real.exp (-(5 * Real.log x)) at he
    rw [Real.exp_neg (5 * Real.log x), he5] at he
    simpa only [one_div] using he
  have h194 : (8 : ℝ) ≤ x ^ (194 : ℕ) := by
    calc
      8 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ x ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (194 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have h187 : (2048 : ℝ) ≤ x ^ (187 : ℕ) := by
    calc
      2048 = (2 : ℝ) ^ (11 : ℕ) := by norm_num
      _ ≤ x ^ (11 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 _
      _ ≤ x ^ (187 : ℕ) := pow_le_pow_right₀ hx1 (by norm_num)
  have hpinL : 8 * x ^ (5 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (194 : ℕ) * x ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right h194 (pow_nonneg hx.le _)
      _ = x ^ (199 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  have hvarL : 2048 * x ^ (12 : ℕ) ≤ L := by
    calc
      _ ≤ x ^ (187 : ℕ) * x ^ (12 : ℕ) :=
        mul_le_mul_of_nonneg_right h187 (pow_nonneg hx.le _)
      _ = x ^ (199 : ℕ) := by rw [← pow_add]
      _ ≤ L := hL
  refine ⟨?_, ?_⟩
  · have hpin : (x + 1) / L ≤ Real.rpow x (-4) / 4 := by
      calc
        _ ≤ (2 * x) / L := div_le_div_of_nonneg_right (by linarith) hLp.le
        _ ≤ (2 * x) / (8 * x ^ (5 : ℕ)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hpinL
        _ = _ := by rw [hρ]; field_simp <;> ring
    have hcoll : x * L ^ 2 / B ≤ Real.rpow x (-4) / 4 := by
      calc
        _ = x * (L ^ 2 / B) := by ring
        _ ≤ x * (Real.exp (-Real.rpow x (1 / 2 : ℝ)) / 4) :=
          mul_le_mul_of_nonneg_left hcollision hx.le
        _ ≤ x * ((1 / x ^ (5 : ℕ)) / 4) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsmall (by norm_num)) hx.le
        _ = _ := by rw [hρ]; field_simp <;> ring
    dsimp only [x] at *
    linarith only [hpin, hcoll]
  · have hpow101 : Real.rpow x (1.01 : ℝ) ≤ x ^ (2 : ℕ) := by
      simpa only [Real.rpow_eq_pow, Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1.01 : ℝ) ≤ 2)
    have hmax : max 1 Checks ≤ Real.exp (3 * Real.rpow x (1.01 : ℝ)) := by
      refine max_le ?_ hchecks
      exact Real.one_le_exp_iff.mpr
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hx.le _))
    have hlog8 : Real.log 8 ≤ 8 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
      linarith
    have hlog : Real.log (8 * max 1 Checks) ≤ 8 + 3 * x ^ (2 : ℕ) := by
      calc
        _ ≤ Real.log (8 * Real.exp (3 * Real.rpow x (1.01 : ℝ))) :=
          Real.log_le_log (by positivity)
            (mul_le_mul_of_nonneg_left hmax (by norm_num))
        _ = Real.log 8 + 3 * Real.rpow x (1.01 : ℝ) := by
          rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0)
            (Real.exp_pos _).ne', Real.log_exp]
        _ ≤ 8 + 3 * x ^ (2 : ℕ) := by nlinarith [hlog8, hpow101]
    have hroot : Real.rpow x (1 / 2 : ℝ) ≤ x := by
      simpa only [Real.rpow_eq_pow, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hpoly : 256 * x ^ (2 : ℕ) ≤ L * Real.rpow x (-4) ^ 2 /
        (8 * x ^ (2 : ℕ)) := by
      calc
        _ = (2048 * x ^ (12 : ℕ)) * Real.rpow x (-4) ^ 2 /
            (8 * x ^ (2 : ℕ)) := by rw [hρ]; field_simp <;> ring
        _ ≤ _ := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hvarL (sq_nonneg _)) (by positivity)
    have hsmallLog : Real.rpow x (1 / 2 : ℝ) + Real.log (8 * max 1 Checks) ≤
        256 * x ^ (2 : ℕ) := by
      nlinarith [hroot, hlog, sq_nonneg (x - 2)]
    exact hsmallLog.trans hpoly

/-! ## Lane B: star/pin physics (Producers.lean, private in the real file). -/

/-- B1 (= run 7's `cluster_failure_dictionary7`).
TeX 16:228–245; estimated proof: 250 lines. -/
theorem cluster_failure_dictionary {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (W : R.Hist C)
    (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh) (Z : ∀ r, S.Val r)
    (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C)
    (s : R.Slice C) (w : EvenRole PT.tiling (G.cellPatch C))
    (hGroup : ∀ z (hz : ¬ IsEvenRole (R.cellWords C (s, z)).1),
      R.groupOf C ⟨(R.cellWords C (s, z)).1, (R.cellWords C (s, z)).2, hz⟩ =
        groups (s, S.groupOf z))
    (hU : ∀ g D y, (R.U C W (groups (s, g)) D).w y = S.U g Z D y)
    (hPrior : ∀ ys fallback,
      R.rawPrior C W ys (R.cellWords C (s, w.1)).1 =
        S.σ w Z (nbrLabels w.1 (R.wordLabel C ys s fallback)))
    (a : R.Group C → Bin PT.tiling (G.cellPatch C)) :
    K.failure C W
      ⟨(R.cellWords C (s, w.1)).1, (R.cellWords C (s, w.1)).2,
        (R.word_parity hc C s w.1).mpr w.2⟩ a =
      Lane_sol_s16_prod1.solver_star_bin_failure S Z w (fun g => a (groups (s, g))) := by
  sorry

/-- B2. Sharp domination of the restricted rows by the raw solver rows:
pretrim loss `h^2 sqrt eps` and permission loss `exp(-cperm n/2)`, with the
cost over at most `h` groups at most 2 (run 7: `permission_retained_sharp7`,
`normalization_product_room7`, `low_cluster_pretrim_power_small7`,
`cluster_permission_cost_room7`).
TeX 16:228–233; estimated proof: 150 lines. -/
theorem cluster_qbar_domination {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k → ∀ C : G.Cell,
      ∃ c : ℝ, 1 ≤ c ∧ c ^ (PT.tiling.P (G.cellPatch C)).h ≤ 2 ∧
        ∀ (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
          (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
          (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C),
          (∀ s V, V ∈ R.slicePass C s ↔ S.AllGood (records s V)) →
          (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) →
          (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) →
          ∀ W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W) →
          ∀ s g D, (K.qbar C W (groups (s, g))).w D ≤ c * S.q g (records s (W s)) D := by
  sorry

/-- B3. Star and pinned-star integrals against the restricted (unpooled)
rows: `solver_star_trimmed_mean` / `solver_star_trimmed_pin_mean` with B2.
TeX 16:228–249; estimated proof: 100 lines. -/
theorem cluster_star_qbar_means {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) {G : LowGeom PT}
      (R : CellRawData G) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      PT.tiling.mode = .lowCluster → n₀ ≤ T.S.n k → ∀ (C : G.Cell)
      (S : SliceSolver κ PT.tiling (G.cellPatch C) PT.mesh)
      (records : ∀ s, R.Value C s ≃ (∀ r, S.Val r))
      (groups : (R.Slice C × HypercubeRamsey.Group PT.tiling (G.cellPatch C)) ≃ R.Group C),
      (∀ s V, V ∈ R.slicePass C s ↔ S.AllGood (records s V)) →
      (∀ W s g D, (R.qraw C W (groups (s, g))).w D = S.q g (records s (W s)) D) →
      (∀ W s g, R.pretrim C W (groups (s, g)) = S.pretrimBins (records s (W s)) g) →
      ∀ W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W) →
      ∀ s (w : EvenRole PT.tiling (G.cellPatch C)),
        (FinLaw.pi fun g => K.qbar C W (groups (s, g))).E
            (Lane_sol_s16_prod1.solver_star_bin_failure S (records s (W s)) w) ≤
          2 * sliceEps κ (PT.tiling.P (G.cellPatch C)).h ∧
        ∀ g D, g ∈ Lane_sol_s16_prod1.solver_star_group_scope S w →
          D ∈ S.pretrimBins (records s (W s)) g →
          (FinLaw.pi (Lane_sol_s16_prod1.coordinatePin
              (fun g => K.qbar C W (groups (s, g))) g D)).E
              (Lane_sol_s16_prod1.solver_star_bin_failure S (records s (W s)) w) ≤
            2 * Real.sqrt (sliceEps κ (PT.tiling.P (G.cellPatch C)).h) := by
  sorry

/-! ## Lane D: the cluster load gate, under the repair. -/

/-- D1. Generic: a product of conditioned laws is the image of a product of
laws on the positive passing values.
TeX 16:259–278; estimated proof: 120 lines. -/
theorem pi_cond_support_map {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
    (P : ∀ i, FinLaw (V i)) (A : ∀ i, Finset (V i))
    (hA : ∀ i, 0 < ∑ v ∈ A i, (P i).w v) :
    ∃ P' : ∀ i, FinLaw {v : V i // v ∈ A i ∧ (P i).w v ≠ 0},
      FinLaw.pi (fun i => FinLaw.cond (P i) (A i) (hA i)) =
        FinLaw.map (FinLaw.pi P') (fun z i => (z i).1) := by
  exact Lane_q_s16_gate1.pi_cond_support_map P A hA

/-- D2. The load summand of one odd role depends on its own slice value.
TeX 16:259–278; estimated proof: 150 lines. -/
theorem cluster_role_term_local {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (R : CellRawData G)
    (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hFallback : ∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
      K.qtilde C pool W g = K.qbar C W g)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster) (C : G.Cell) (pool : CellPool G C)
    (W W' : R.Hist C) (hW : (R.history C).w W ≠ 0) (hW' : (R.history C).w W' ≠ 0)
    (r : OddCellRole G C)
    (heq : W ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1 = W' ((R.cellWords C).symm ⟨r.1, r.2.1⟩).1)
    (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y =
      ∑ b, (K.qtilde C pool W' (R.groupOf C r)).w b * (R.U C W' (R.groupOf C r) b).w y := by
  exact Lane_q_s16_gate1.cluster_role_term_local R Perm K hFallback hR hc C pool W W'
    hW hW' r heq y

/-- D3. Per-role cap at pools whose normalizers pass (typical pools).
TeX 16:274–276; estimated proof: 150 lines. -/
theorem cluster_role_term_cap {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) (pool : CellPool H.geom C) (W : R.Hist C) (hW : (R.history C).w W ≠ 0)
    (hn4 : Real.rpow (T.S.n k : ℝ) (-4) ≤ 1 / 2)
    (hmass : ∀ g, (1 - Real.rpow (T.S.n k : ℝ) (-4)) *
      ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b)
    (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) :
    ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y ≤
      64 * Real.exp (2 * (sliceK κ (PT.tiling.P (H.geom.cellPatch C)).h : ℝ) *
        sliceT κ (PT.tiling.P (H.geom.cellPatch C)).h) / (H.geom.nslot C : ℝ) := by
  exact Lane_q_s16_gate1.cluster_role_term_cap hκ Q H R Perm K hR hc hPerm C pool W hW hn4
    hmass r y

/-- D4. Per-role history mean at typical pools, through `low_profile` and
`law_cap` (T16:268-273): `4 (B/L) * 11/M`.
TeX 16:268–273; estimated proof: 350 lines. -/
theorem cluster_role_term_mean {κ : CConsts} (hκ : κ.Admissible)
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
    (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
    (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm)
    (hR : R.SourceValid) (hc : PT.tiling.mode.isCluster)
    (hPerm : ∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W))
    (C : H.geom.Cell) (pool : CellPool H.geom C)
    (hn4 : Real.rpow (T.S.n k : ℝ) (-4) ≤ 1 / 2)
    (hmass : ∀ W, (R.history C).w W ≠ 0 → ∀ g, (1 - Real.rpow (T.S.n k : ℝ) (-4)) *
      ((H.geom.nslot C : ℝ) / Fintype.card (Bin PT.tiling (H.geom.cellPatch C))) ≤
        ∑ b ∈ Finset.univ.image pool, (K.qbar C W g).w b)
    (r : OddCellRole H.geom C) (y : Fin (T.S.N k)) :
    (R.history C).E (fun W =>
      ∑ b, (K.qtilde C pool W (R.groupOf C r)).w b * (R.U C W (R.groupOf C r) b).w y) ≤
      44 / ((H.geom.nslot C : ℝ) * (PT.tiling.P (H.geom.cellPatch C)).d) := by
  sorry

/-- D5. Numerical room of the gate variance budget. Here `words = 2^h`,
`A = exp(2kT)` and `slices * words` is the cell size.
TeX 16:274–278; estimated proof: 120 lines. -/
theorem cluster_gate_budget_room {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ (n : ℕ) (L slices words A N : ℝ),
      n₀ ≤ n → 2 ≤ n → (n : ℝ) ^ (199 : ℕ) ≤ L → 0 ≤ slices → 1 ≤ words → words ≤ n →
      slices * words ≤ (n : ℝ) ^ (200 : ℕ) → 1 ≤ A → A ≤ n → 1 ≤ N → N ≤ n * 2 ^ n →
      (Real.rpow (n : ℝ) (1 / 2 : ℝ) + Real.log (max 1 N)) *
          (slices * (words * (64 * A / L)) ^ 2) ≤ 2 * (κ.θstar / 2) ^ 2 := by
  sorry

/-- D6. The cluster gate (assembled from D1-D5 plus Link/checks_cover).
TeX 16:259–278; estimated proof: 250 lines. -/
theorem cluster_load_gate {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom) (Perm : CellPermissions R) (K : CellRestrictedKernels R Perm),
      (∀ C pool W g, (∑ D ∈ Finset.univ.image pool, (K.qbar C W g).w D) = 0 →
        K.qtilde C pool W g = K.qbar C W g) →
      R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      (∀ C W, (R.history C).w W ≠ 0 → PermissionLossHypotheses (Perm.table C) (R.qin C W)) →
      ∀ (C : H.geom.Cell) {Check : Type} [Fintype Check]
        (D : CellPoolDiagnostics (Fin (H.geom.nslot C)) (Bin PT.tiling (H.geom.cellPatch C))
          (R.Hist C) Check (T.S.n k) (1 / 2)),
        CellDiagnosticLink K C D → Nonempty (LoadGateHypotheses D) := by
  sorry

/-! ## Assembly. -/

/-- Star checks (`none`) and pinned-star checks (`some (g, b)`), indexed by a
positive passing slice value, never by a whole-cell history. -/
abbrev ClusterStarCheck {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} (R : CellRawData G) (C : G.Cell) :=
  (s : R.Slice C) × ({z : R.Value C s // z ∈ R.slicePass C s ∧ (R.sliceLaw C s).w z ≠ 0} ×
    EvenRole PT.tiling (G.cellPatch C) ×
    Option (HypercubeRamsey.Group PT.tiling (G.cellPatch C) × Bin PT.tiling (G.cellPatch C)))

/-- E1. Total check count (normalizer rows from `cluster_normalizer_setup`,
`hrowCount`, plus star/pin checks): cell size, `low_support`, `2^h <= n`
from the amplitude room, and `#bins <= N <= n 2^n`.
TeX 16:249–257; estimated proof: 100 lines. -/
theorem cluster_check_count {κ : CConsts} (hκ : κ.Admissible) :
    ∃ n₀ : ℕ, ∀ {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {K16 : ℝ}
      (Q : LowModeQuantFacts hκ (PT := PT) K16) (H : LowGeometryCertificate hκ Q)
      (R : CellRawData H.geom), R.SourceValid → PT.tiling.mode.isCluster → n₀ ≤ T.S.n k →
      ∀ (C : H.geom.Cell) (NormalizerCheck : Type) [Fintype NormalizerCheck],
        (Fintype.card NormalizerCheck : ℝ) ≤
          (T.S.n k : ℝ) ^ (200 : ℕ) * Real.exp ((T.S.n k : ℝ) ^ (1.01 : ℝ)) →
        (Fintype.card (NormalizerCheck ⊕ ClusterStarCheck R C) : ℝ) ≤
          Real.exp (3 * (T.S.n k : ℝ) ^ (1.01 : ℝ)) := by
  exact Lane_q_s16_conc.total_check_count hκ


end HypercubeRamsey.S16.ClusterDiagnostics
