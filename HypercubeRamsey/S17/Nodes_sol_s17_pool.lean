import HypercubeRamsey.S17.Nodes_q_s17_pool

namespace HypercubeRamsey.Lane_sol_s17_pool

open Classical
open scoped BigOperators

/-- Integrating the first coordinate of an independent finite experiment. -/
theorem pi_pr_cons {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin (n + 1) → FinLaw α) (A : (Fin (n + 1) → α) → Prop) :
    (FinLaw.pi P).pr A = (P 0).E (fun y =>
      (FinLaw.pi fun i : Fin n => P i.succ).pr (fun ys => A (Fin.cons y ys))) := by
  classical
  unfold FinLaw.pr FinLaw.E
  change (∑ ys, if A ys then ∏ i, (P i).w (ys i) else 0) = _
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => α)) _ _ (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  change (if A (Fin.cons y ys) then ∏ i, (P i).w ((Fin.cons y ys : Fin (n + 1) → α) i) else 0) =
    (P 0).w y * (if A (Fin.cons y ys) then (FinLaw.pi fun i : Fin n => P i.succ).w ys else 0)
  by_cases hA : A (Fin.cons y ys)
  · simp [FinLaw.pi, hA, Fin.prod_univ_succ]
  · simp [hA]

private theorem pr_le_one {α : Type*} [Fintype α] (P : FinLaw α) (A : α → Prop) :
    P.pr A ≤ 1 := by
  classical
  calc
    P.pr A ≤ ∑ a, P.w a := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs <;> simp [P.nonneg a]
    _ = 1 := P.sum_one

/-- Row mass after finitely many independent nonnegative factors. -/
noncomputable def productMass {N d : ℕ} {α : Type*}
    (μ : Law N) (f : Fin d → Fin N → α → ℝ) (ys : Fin d → α) : ℝ :=
  ∑ x, μ.w x * ∏ i, f i x (ys i)

/-- Normalizing the first restriction separates its mass from the remaining row. -/
theorem productMass_cons {N n : ℕ} {α : Type*} (μ : Law N)
    (f : Fin (n + 1) → Fin N → α → ℝ) (y : α) (ys : Fin n → α)
    (hf : ∀ x, 0 ≤ f 0 x y) (Z : ℝ) (hZ : 0 < Z)
    (hZeq : ∑ x, μ.w x * f 0 x y = Z) :
    productMass μ f (Fin.cons y ys) = Z *
      productMass (Lane_q_s17_pool.reweightLaw μ (fun x => f 0 x y) hf Z hZ hZeq)
        (fun i => f i.succ) ys := by
  classical
  unfold productMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Lane_q_s17_pool.reweightLaw]
  field_simp

/-- A successful restriction preserves the atom budget for the next exposure. -/
theorem reweight_cap_step {N n : ℕ} (μ : Law N) (f : Fin N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (Z : ℝ) (hZ : 0 < Z)
    (hZeq : ∑ x, μ.w x * f x = Z) (B q C : ℝ)
    (hB : 0 ≤ B) (hq : 0 < q) (hC : 0 < C) (hqZ : q ≤ Z)
    (hμ : μ.CapLE (B * (q / C) ^ (n + 1))) (hfC : ∀ x, f x ≤ C) :
    (Lane_q_s17_pool.reweightLaw μ f hf Z hZ hZeq).CapLE
      (B * (q / C) ^ n) := by
  intro x
  change (N : ℝ) * (μ.w x * f x / Z) ≤ _
  have hmul : (N : ℝ) * μ.w x * f x ≤ B * (q / C) ^ (n + 1) * C :=
    mul_le_mul (hμ x) (hfC x) (hf x) (by positivity)
  calc
    (N : ℝ) * (μ.w x * f x / Z) = ((N : ℝ) * μ.w x * f x) / Z := by ring
    _ ≤ (B * (q / C) ^ (n + 1) * C) / Z :=
      div_le_div_of_nonneg_right hmul hZ.le
    _ ≤ (B * (q / C) ^ (n + 1) * C) / q :=
      div_le_div_of_nonneg_left (by positivity) hq hqZ
    _ = B * (q / C) ^ n := by rw [pow_succ]; field_simp

/-- Uniform one-step tails multiply into a lower-mass estimate even though
successive normalized rows depend on all earlier labels. -/
theorem adaptive_product_lower_tail {N : ℕ} {α : Type*} [Fintype α]
    (X : Finset (Fin N)) (B q C ε : ℝ)
    (hB : 0 ≤ B) (hq : 0 < q) (hC : 0 < C) (hqC : q ≤ C) (hε : 0 ≤ ε)
    (n : ℕ) : ∀ (μ : Law N) (P : Fin n → FinLaw α)
      (f : Fin n → Fin N → α → ℝ),
      μ.SupportedIn X → μ.CapLE (B * (q / C) ^ n) →
      (∀ i x y, 0 ≤ f i x y) → (∀ i x y, f i x y ≤ C) →
      (∀ i (ν : Law N), ν.SupportedIn X → ν.CapLE B →
        (P i).pr (fun y => (∑ x, ν.w x * f i x y) < q) ≤ ε) →
      (FinLaw.pi P).pr (fun ys => productMass μ f ys < q ^ n) ≤ (n : ℝ) * ε := by
  classical
  induction n with
  | zero =>
    intro μ P f hsup hcap hf hfC htail
    have hmass : ∀ ys, productMass μ f ys = 1 := by
      intro ys
      simp [productMass, μ.sum_eq_one]
    simp [FinLaw.pr, hmass]
  | succ n ih =>
    intro μ P f hsup hcap hf hfC htail
    have hr0 : 0 ≤ q / C := (div_pos hq hC).le
    have hr1 : q / C ≤ 1 := (div_le_one hC).2 hqC
    have hcapB : μ.CapLE B := by
      intro x
      exact (hcap x).trans (by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1) hB)
    let Z : α → ℝ := fun y => ∑ x, μ.w x * f 0 x y
    let P' : Fin n → FinLaw α := fun i => P i.succ
    let f' : Fin n → Fin N → α → ℝ := fun i => f i.succ
    let g : α → ℝ := fun y =>
      (FinLaw.pi P').pr (fun ys => productMass μ f (Fin.cons y ys) < q ^ (n + 1))
    have hg : ∀ y, g y ≤ (if Z y < q then 1 else 0) + (n : ℝ) * ε := by
      intro y
      by_cases hbad : Z y < q
      · simp only [ite_eq_left hbad]
        have hprob := pr_le_one (FinLaw.pi P')
          (fun ys => productMass μ f (Fin.cons y ys) < q ^ (n + 1))
        have hnε : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
        dsimp [g]
        linarith
      · have hqZ : q ≤ Z y := le_of_not_gt hbad
        have hZ : 0 < Z y := hq.trans_le hqZ
        let ν : Law N := Lane_q_s17_pool.reweightLaw μ (fun x => f 0 x y)
          (hf 0 · y) (Z y) hZ rfl
        have hνsup : ν.SupportedIn X := by
          intro x hx
          simp [ν, Lane_q_s17_pool.reweightLaw, hsup x hx]
        have hνcap : ν.CapLE (B * (q / C) ^ n) :=
          reweight_cap_step μ (fun x => f 0 x y) (hf 0 · y)
            (Z y) hZ rfl B q C hB hq hC hqZ hcap (hfC 0 · y)
        have hνtail := ih ν P' f' hνsup hνcap
          (fun i x y => hf i.succ x y) (fun i x y => hfC i.succ x y)
          (fun i τ hτsup hτcap => htail i.succ τ hτsup hτcap)
        have hmono : g y ≤ (FinLaw.pi P').pr
            (fun ys => productMass ν f' ys < q ^ n) := by
          apply Lane_q_s17_pool.pr_mono
          intro ys hys
          have hsplit := productMass_cons μ f y ys (hf 0 · y) (Z y) hZ rfl
          change productMass μ f (Fin.cons y ys) < q ^ (n + 1) at hys
          by_contra hn
          have hmass : q ^ n ≤ productMass ν f' ys := le_of_not_gt hn
          have hprod : q ^ (n + 1) ≤ Z y * productMass ν f' ys := by
            rw [pow_succ]
            calc
              q ^ n * q ≤ q ^ n * Z y :=
                mul_le_mul_of_nonneg_left hqZ (pow_nonneg hq.le _)
              _ ≤ productMass ν f' ys * Z y :=
                mul_le_mul_of_nonneg_right hmass hZ.le
              _ = _ := by ring
          rw [hsplit] at hys
          exact (not_lt_of_ge hprod) hys
        simpa [hbad] using hmono.trans hνtail
    rw [pi_pr_cons]
    change (P 0).E g ≤ _
    have hE : (P 0).E g ≤ (P 0).pr (fun y => Z y < q) + (n : ℝ) * ε := by
      calc
        (P 0).E g ≤ ∑ y, (P 0).w y *
            ((if Z y < q then 1 else 0) + (n : ℝ) * ε) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hg y) ((P 0).nonneg y)
        _ = (P 0).pr (fun y => Z y < q) + (n : ℝ) * ε := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, (P 0).sum_one, one_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro y hy
          split_ifs <;> simp
    have hfirst : (P 0).pr (fun y => Z y < q) ≤ ε := htail 0 μ hsup hcapB
    push_cast
    linarith [hE, hfirst]

/-- Deep discrepancy controls a short sequence of independent pinned hits,
including all normalized intermediate first-side laws. -/
theorem independent_hits_lower_tail {T : Stage} {k n : ℕ}
    {wS wL err W : ℝ} (hDisc : TwoBudgetDisc T k wS wL err)
    (c : Colour) (μ : Law (T.S.N k)) (ν : Fin n → Law (T.S.N k))
    (hμ : μ.SupportedIn (T.X k))
    (herr : 0 < (1 / 2 : ℝ) - err) (herr0 : 0 ≤ err)
    (hcap : μ.CapLE (Real.exp wS * (1 / 2 - err) ^ n))
    (hν : ∀ i, (ν i).SupportedIn (T.Y k))
    (hνW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr
      (fun ys => productMass μ (fun _ x y => hit (T.S.E k) c x y) ys <
        (1 / 2 - err) ^ n) ≤ (n : ℝ) * (2 * Real.exp (W - wL)) := by
  classical
  apply adaptive_product_lower_tail (T.X k) (Real.exp wS) (1 / 2 - err) 1
    (2 * Real.exp (W - wL)) (Real.exp_pos wS).le herr (by norm_num)
    (by linarith) (by positivity) n μ
    (fun i => ListGateContext.lawAsFinLaw (ν i)) (fun _ x y => hit (T.S.E k) c x y)
    hμ (by simpa using hcap)
  · intro i x y
    unfold hit
    split_ifs <;> norm_num
  · intro i x y
    unfold hit
    split_ifs <;> norm_num
  · intro i τ hτ hτcap
    have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
    have hτw : τ.WidthLE wS := fun x =>
      (le_div_iff₀ hN).2 (by simpa [mul_comm] using hτcap x)
    have htail := S12.exceptional_second hDisc c
      (Or.inl ⟨le_rfl, le_rfl⟩) τ hτ hτw (ν i) (hν i) (hνW i)
    have hmono : (ListGateContext.lawAsFinLaw (ν i)).pr
        (fun y => (∑ x, τ.w x * hit (T.S.E k) c x y) < 1 / 2 - err) ≤
      (ListGateContext.lawAsFinLaw (ν i)).pr
        (fun y => err < |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|) := by
      apply Lane_q_s17_pool.pr_mono
      intro y hy
      have habs := neg_le_abs ((∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2)
      linarith
    exact hmono.trans (by simpa [FinLaw.pr, ListGateContext.lawAsFinLaw,
      Finset.sum_filter] using htail)

/-- A short sequence of independent crossing hit ratios retains mass.
The denominator window is required only on the cleaned first-side support. -/
theorem independent_hitRatios_lower_tail {T : Stage} {k n : ℕ}
    {wS wL err W dmin dmax : ℝ} (hDisc : TwoBudgetDisc T k wS wL err)
    (c : Colour) (X : Finset (Fin (T.S.N k))) (hX : X ⊆ T.X k)
    (μ : Law (T.S.N k)) (ν : Fin n → Law (T.S.N k))
    (d : Fin n → Fin (T.S.N k) → ℝ)
    (hμ : μ.SupportedIn X) (hmin : 0 < dmin) (hmax : 0 < dmax)
    (herr : 0 < (1 / 2 : ℝ) - err)
    (hgap : (1 / 2 - err) / dmax ≤ 1 / dmin)
    (hcap : μ.CapLE (Real.exp wS * (((1 / 2 - err) / dmax) / (1 / dmin)) ^ n))
    (hdmin : ∀ i x, x ∈ X → dmin ≤ d i x)
    (hdmax : ∀ i x, x ∈ X → d i x ≤ dmax)
    (hν : ∀ i, (ν i).SupportedIn (T.Y k))
    (hνW : ∀ i, (ν i).WidthLE W) :
    (FinLaw.pi fun i => ListGateContext.lawAsFinLaw (ν i)).pr
      (fun ys => productMass μ (fun i x y => if x ∈ X then
        hit (T.S.E k) c x y / d i x else 0) ys <
        ((1 / 2 - err) / dmax) ^ n) ≤ (n : ℝ) * (2 * Real.exp (W - wL)) := by
  classical
  have hdpos : ∀ i x, x ∈ X → 0 < d i x :=
    fun i x hx => hmin.trans_le (hdmin i x hx)
  apply adaptive_product_lower_tail X (Real.exp wS) ((1 / 2 - err) / dmax)
    (1 / dmin) (2 * Real.exp (W - wL)) (Real.exp_pos wS).le
    (div_pos herr hmax) (by positivity) hgap (by positivity) n μ
    (fun i => ListGateContext.lawAsFinLaw (ν i))
    (fun i x y => if x ∈ X then hit (T.S.E k) c x y / d i x else 0) hμ hcap
  · intro i x y
    split_ifs with hx
    · exact div_nonneg (by unfold hit; split_ifs <;> norm_num) (hdpos i x hx).le
    · exact le_rfl
  · intro i x y
    split_ifs with hx
    · by_cases hh : Hits (T.S.E k) c x y
      · simp only [hit, ite_eq_left hh]
        exact one_div_le_one_div_of_le hmin (hdmin i x hx)
      · simp [hit, hh, hmin.le]
    · positivity
  · intro i τ hτ hτcap
    have hτX : τ.SupportedIn (T.X k) := by
      intro x hx
      exact hτ x (fun hxX => hx (hX hxX))
    have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
    have hτw : τ.WidthLE wS := fun x =>
      (le_div_iff₀ hN).2 (by simpa [mul_comm] using hτcap x)
    have htail := S12.exceptional_second hDisc c
      (Or.inl ⟨le_rfl, le_rfl⟩) τ hτX hτw (ν i) (hν i) (hνW i)
    have hmono : (ListGateContext.lawAsFinLaw (ν i)).pr
        (fun y => (∑ x, τ.w x * (if x ∈ X then
          hit (T.S.E k) c x y / d i x else 0)) < (1 / 2 - err) / dmax) ≤
      (ListGateContext.lawAsFinLaw (ν i)).pr
        (fun y => err < |(∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2|) := by
      apply Lane_q_s17_pool.pr_mono
      intro y hy
      have heq : (∑ x, τ.w x * (if x ∈ X then
          hit (T.S.E k) c x y / d i x else 0)) =
          ∑ x, τ.w x * (hit (T.S.E k) c x y / d i x) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxX : x ∈ X
        · simp [hxX]
        · simp [hxX, hτ x hxX]
      rw [heq] at hy
      have hlower := Lane_q_s17_pool.hitRatio_average_lower τ (T.S.E k) c y (d i) dmax
        (fun x hx => hdpos i x (by by_contra hn; exact hx (hτ x hn)))
        (fun x hx => hdmax i x (by by_contra hn; exact hx (hτ x hn)))
      have hdegree : (∑ x, τ.w x * hit (T.S.E k) c x y) < 1 / 2 - err :=
        (div_lt_div_iff_of_pos_right hmax).mp (hlower.trans_lt hy)
      have habs := neg_le_abs ((∑ x, τ.w x * hit (T.S.E k) c x y) - 1 / 2)
      linarith
    exact hmono.trans (by simpa [FinLaw.pr, ListGateContext.lawAsFinLaw,
      Finset.sum_filter] using htail)

/-- The pool moment is the probability that independent fresh trials sharing
those pools all fail, with the same typicality and compatibility indicators. -/
theorem repeated_trials_identity {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (v : Pos T k) (μ : FinLaw D.PoolAssignment) (m : ℕ) :
    μ.E (fun pools => if D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools then
      (D.freshEventProbability v pools) ^ m else 0) =
    (FinLaw.bind μ (fun pools => FinLaw.pi fun _ : Fin m => D.freshConfigLaw pools)).pr
      (fun ω => D.LocalPoolsTypical v ω.1 ∧ D.compatiblePool v ω.1 ∧
        ∀ j, D.event v (ω.2 j)) := by
  classical
  unfold FinLaw.E FinLaw.pr
  simp only [FinLaw.bind]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro pools hpools
  have hprod := Lane_q_s17_pool.pi_pr_forall
    (fun _ : Fin m => D.freshConfigLaw pools) (fun _ s => D.event v s)
  have hpow : (FinLaw.pi fun _ : Fin m => D.freshConfigLaw pools).pr
      (fun trials => ∀ j, D.event v (trials j)) = (D.freshEventProbability v pools) ^ m := by
    simpa [ListGateContext.freshEventProbability] using hprod
  by_cases hgood : D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools
  · simp only [hgood.1, hgood.2, true_and, ite_true]
    rw [← hpow, FinLaw.pr, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro trials htrials
    by_cases hb : ∀ j, D.event v (trials j)
    · simp [hb]
    · simp [hb]
  · have hpoint : ∀ trials : Fin m → Config D.F,
        ¬ (D.LocalPoolsTypical v pools ∧ D.compatiblePool v pools ∧
          ∀ j, D.event v (trials j)) := by
      intro trials ht
      exact hgood ⟨ht.1, ht.2.1⟩
    simp [hgood, hpoint]

/-- A fixed within-bin index, chosen consistently before the random bin. -/
noncomputable def binIndexRead {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (B : Bin PT.tiling i) (j : Fin (PT.tiling.P i).d) : Fin (T.S.N k) :=
  ((B.1.equivFin).symm (Fin.cast (hPT.tiling_valid.bins_card i B.1 B.2).symm j)).1

theorem binIndexRead_mem {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (B : Bin PT.tiling i) (j : Fin (PT.tiling.P i).d) : binIndexRead hPT i B j ∈ B.1 :=
  ((B.1.equivFin).symm (Fin.cast (hPT.tiling_valid.bins_card i B.1 B.2).symm j)).2

theorem binIndexRead_injective {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (j : Fin (PT.tiling.P i).d) : Function.Injective (fun B => binIndexRead hPT i B j) := by
  intro B C hBC
  apply Subtype.ext
  exact (PT.tiling.P i).bins.eq_of_mem_parts B.2 C.2 (binIndexRead_mem hPT i B j)
    (by
      change binIndexRead hPT i B j ∈ C.1
      change binIndexRead hPT i B j = binIndexRead hPT i C j at hBC
      rw [hBC]
      exact binIndexRead_mem hPT i C j)

private theorem bins_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m) :
    (Finset.univ : Finset (Bin PT.tiling i)).Nonempty := by
  obtain ⟨y, hy⟩ := (hPT.tiling_valid.patch_nonempty i).2
  obtain ⟨B, hB, _⟩ := (PT.tiling.P i).bins.exists_mem hy
  exact ⟨⟨B, hB⟩, Finset.mem_univ _⟩

/-- Label law obtained from a uniform physical bin at a prescribed in-bin index. -/
noncomputable def binIndexLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (j : Fin (PT.tiling.P i).d) : Law (T.S.N k) :=
  let P := FinLaw.map (FinLaw.uniform Finset.univ (bins_nonempty hPT i))
    (fun B => binIndexRead hPT i B j)
  { w := P.w, nonneg := P.nonneg, sum_eq_one := P.sum_one }

/-- One prescribed index in a uniform bin has at most one preimage per label. -/
theorem binIndexLaw_atom_bound {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (j : Fin (PT.tiling.P i).d) (y : Fin (T.S.N k)) :
    (binIndexLaw hPT i j).w y ≤ 1 / (Fintype.card (Bin PT.tiling i) : ℝ) := by
  classical
  change (∑ B : Bin PT.tiling i, if binIndexRead hPT i B j = y then
    (FinLaw.uniform Finset.univ (bins_nonempty hPT i)).w B else 0) ≤ _
  simp only [FinLaw.uniform, Finset.mem_univ, ite_true, Finset.card_univ]
  by_cases hex : ∃ B, binIndexRead hPT i B j = y
  · obtain ⟨B, hB⟩ := hex
    rw [Finset.sum_eq_single B]
    · simp [hB]
    · intro C hC hne
      have hc : binIndexRead hPT i C j ≠ y := by
        intro heq
        exact hne (binIndexRead_injective hPT i j (heq.trans hB.symm))
      simp [hc]
    · simp
  · have hz : ∀ B : Bin PT.tiling i, binIndexRead hPT i B j ≠ y := by
      intro B hB
      exact hex ⟨B, hB⟩
    simp [hz]

theorem binIndexLaw_supported {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (j : Fin (PT.tiling.P i).d) : (binIndexLaw hPT i j).SupportedIn (T.Y k) := by
  intro y hy
  change (∑ B : Bin PT.tiling i, if binIndexRead hPT i B j = y then
    (FinLaw.uniform Finset.univ (bins_nonempty hPT i)).w B else 0) = 0
  apply Finset.sum_eq_zero
  intro B hB
  have hmem : binIndexRead hPT i B j ∈ T.Y k :=
    (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.2.2
      ((hPT.tiling_valid.patch_supports i).2.2.1
        ((PT.tiling.P i).bins.le B.2 (binIndexRead_mem hPT i B j))))).1
  have hne : binIndexRead hPT i B j ≠ y := by intro heq; exact hy (heq ▸ hmem)
  simp [hne]

/-- The width cost for prescribing an in-bin index is the log host/bin ratio. -/
theorem binIndexLaw_width {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (j : Fin (PT.tiling.P i).d) : (binIndexLaw hPT i j).WidthLE
      (Real.log ((T.S.N k : ℝ) / Fintype.card (Bin PT.tiling i))) := by
  have hN : 0 < (T.S.N k : ℝ) := by exact_mod_cast T.S.N_pos k
  have hB : 0 < (Fintype.card (Bin PT.tiling i) : ℝ) := by
    exact_mod_cast (by simpa using Finset.card_pos.mpr (bins_nonempty hPT i) :
      0 < Fintype.card (Bin PT.tiling i))
  intro y
  rw [Real.exp_log (div_pos hN hB)]
  calc
    (binIndexLaw hPT i j).w y ≤ 1 / (Fintype.card (Bin PT.tiling i) : ℝ) :=
      binIndexLaw_atom_bound hPT i j y
    _ = (T.S.N k : ℝ) / Fintype.card (Bin PT.tiling i) / T.S.N k := by field_simp

/-- Integrating the first coordinate of a product-law expectation. -/
theorem pi_E_cons {α : Type*} [Fintype α] {n : ℕ}
    (P : Fin (n + 1) → FinLaw α) (F : (Fin (n + 1) → α) → ℝ) :
    (FinLaw.pi P).E F = (P 0).E (fun y =>
      (FinLaw.pi fun i : Fin n => P i.succ).E (fun ys => F (Fin.cons y ys))) := by
  classical
  unfold FinLaw.E
  change (∑ ys, (∏ i, (P i).w (ys i)) * F ys) = _
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => α)) _ _
    (fun _ => rfl), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys hys
  change (∏ i, (P i).w ((Fin.cons y ys : Fin (n + 1) → α) i)) * F (Fin.cons y ys) =
    (P 0).w y * ((∏ i : Fin n, (P i.succ).w (ys i)) * F (Fin.cons y ys))
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

/-- Repeat rank counts visits to slots already seen, including initially pinned slots. -/
noncomputable def repeatRank {α : Type*} [DecidableEq α] :
    (n : ℕ) → Finset α → (Fin n → α) → ℕ
  | 0, _, _ => 0
  | n + 1, S, ys => (if ys 0 ∈ S then 1 else 0) +
      repeatRank n (insert (ys 0) S) (fun i => ys i.succ)

private theorem pr_mem_le {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (S : Finset α) (C : ℝ) (hC : ∀ y, P.w y ≤ C) :
    P.pr (fun y => y ∈ S) ≤ (S.card : ℝ) * C := by
  classical
  have heq : P.pr (fun y => y ∈ S) = ∑ y ∈ S, P.w y := by
    unfold FinLaw.pr
    rw [← Finset.sum_subset (Finset.subset_univ S) (by
      intro y hy hyn
      simp [hyn])]
    apply Finset.sum_congr rfl
    intro y hy
    simp [hy]
  rw [heq]
  calc
    ∑ y ∈ S, P.w y ≤ ∑ _y ∈ S, C := Finset.sum_le_sum fun y _ => hC y
    _ = _ := by simp

/-- An exponential moment for collision rank. This avoids enumerating equality
patterns and applies to different slot laws with a common atom bound. -/
theorem independent_repeat_rank_moment {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (L a : ℝ) (hL : 0 < L) (ha : 1 ≤ a) (n : ℕ) :
    ∀ (P : Fin n → FinLaw α) (S : Finset α), S.card + n ≤ m →
      (∀ i y, (P i).w y ≤ 1 / L) →
      (FinLaw.pi P).E (fun ys => a ^ repeatRank n S ys) ≤
        (1 + (m : ℝ) * a / L) ^ n := by
  classical
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  let q : ℝ := 1 + (m : ℝ) * a / L
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  induction n with
  | zero =>
    intro P S hS hP
    simp [repeatRank, FinLaw.E, FinLaw.pi]
  | succ n ih =>
    intro P S hS hP
    let P' : Fin n → FinLaw α := fun i => P i.succ
    have hinner : ∀ y, (FinLaw.pi P').E
        (fun ys => a ^ repeatRank n (insert y S) ys) ≤ q ^ n := by
      intro y
      apply ih P' (insert y S)
      · have hc := Finset.card_insert_le y S
        omega
      · intro i z
        exact hP i.succ z
    have hfirst : (P 0).pr (fun y => y ∈ S) ≤ (m : ℝ) / L := by
      calc
        (P 0).pr (fun y => y ∈ S) ≤ (S.card : ℝ) * (1 / L) :=
          pr_mem_le (P 0) S (1 / L) (hP 0)
        _ ≤ (m : ℝ) * (1 / L) := by
          apply mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : S.card ≤ m))
            (by positivity)
        _ = _ := by ring
    have hfactor : (P 0).E (fun y => a ^ (if y ∈ S then 1 else 0)) ≤ q := by
      calc
        (P 0).E (fun y => a ^ (if y ∈ S then 1 else 0)) ≤
            ∑ y, (P 0).w y * (1 + if y ∈ S then a else 0) := by
          apply Finset.sum_le_sum
          intro y hy
          apply mul_le_mul_of_nonneg_left _ ((P 0).nonneg y)
          by_cases hyS : y ∈ S <;> simp [hyS]
        _ = 1 + a * (P 0).pr (fun y => y ∈ S) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          simp only [mul_one, (P 0).sum_one]
          congr 1
          rw [FinLaw.pr, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          by_cases hyS : y ∈ S <;> simp [hyS, mul_comm]
        _ ≤ 1 + a * ((m : ℝ) / L) := by gcongr
        _ = q := by dsimp [q]; ring
    rw [pi_E_cons]
    change (P 0).E (fun y => (FinLaw.pi P').E
      (fun ys => a ^ repeatRank (n + 1) S (Fin.cons y ys))) ≤ _
    calc
      _ = (P 0).E (fun y => a ^ (if y ∈ S then 1 else 0) *
          (FinLaw.pi P').E (fun ys => a ^ repeatRank n (insert y S) ys)) := by
        unfold FinLaw.E
        apply Finset.sum_congr rfl
        intro y hy
        congr 1
        dsimp only
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ys hys
        simp only [repeatRank, Fin.cons_zero, Fin.cons_succ, pow_add]
        ring
      _ ≤ (P 0).E (fun y => a ^ (if y ∈ S then 1 else 0) * q ^ n) := by
        apply Finset.sum_le_sum
        intro y hy
        apply mul_le_mul_of_nonneg_left _ ((P 0).nonneg y)
        exact mul_le_mul_of_nonneg_left (hinner y) (pow_nonneg ha0 _)
      _ = (P 0).E (fun y => a ^ (if y ∈ S then 1 else 0)) * q ^ n := by
        unfold FinLaw.E
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ ≤ q * q ^ n := mul_le_mul_of_nonneg_right hfactor (pow_nonneg hq0 _)
      _ = (1 + (m : ℝ) * a / L) ^ (n + 1) := by dsimp [q]; rw [pow_succ]; ring

/-- At most twice the overlap rank many occurrences use repeated or pinned
slots. Every repeated unpinned slot has at least two occurrences. -/
theorem nonunique_occurrences_le_two_rank {ι α : Type*} [Fintype ι]
    [DecidableEq ι] [DecidableEq α] (f : ι → α) (pinned : Finset α) :
    (Finset.univ.filter fun i : ι => f i ∈ pinned ∨
      2 ≤ (Finset.univ.filter fun j : ι => f j = f i).card).card ≤
    2 * (Fintype.card ι - ((Finset.univ.image f) \ pinned).card) := by
  classical
  let U : Finset α := (Finset.univ.image f) \ pinned
  let bad : Finset ι := Finset.univ.filter fun i => f i ∈ pinned ∨
    2 ≤ (Finset.univ.filter fun j => f j = f i).card
  let good : Finset ι := Finset.univ \ bad
  let fiber : α → Finset ι := fun y => Finset.univ.filter fun i => f i = y
  have hpoint : ∀ y ∈ U, 2 ≤ (fiber y).card + (good.filter fun i => f i = y).card := by
    intro y hy
    have hy' := Finset.mem_sdiff.mp hy
    obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hy'.1
    have hpos : 1 ≤ (fiber y).card := by
      have hne : (fiber y).Nonempty := ⟨i, by simp [fiber, hfi]⟩
      exact Finset.card_pos.mpr hne
    by_cases htwo : 2 ≤ (fiber y).card
    · omega
    · have hsub : fiber y ⊆ good.filter fun i => f i = y := by
        intro j hj
        have hfj : f j = y := (Finset.mem_filter.mp hj).2
        have hjgood : j ∈ good := by
          apply Finset.mem_sdiff.mpr
          refine ⟨Finset.mem_univ j, ?_⟩
          intro hjbad
          have hbad := (Finset.mem_filter.mp hjbad).2
          rcases hbad with hp | hc
          · exact hy'.2 (hfj ▸ hp)
          · apply htwo
            simpa [fiber, hfj] using hc
        exact Finset.mem_filter.mpr ⟨hjgood, hfj⟩
      have hle := Finset.card_le_card hsub
      omega
  have hsum : 2 * U.card ≤
      (∑ y ∈ U, (fiber y).card) + ∑ y ∈ U, (good.filter fun i => f i = y).card := by
    calc
      2 * U.card = ∑ _y ∈ U, (2 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ U, ((fiber y).card + (good.filter fun i => f i = y).card) :=
        Finset.sum_le_sum hpoint
      _ = _ := Finset.sum_add_distrib
  have hfiber : (∑ y ∈ U, (fiber y).card) ≤ Fintype.card ι := by
    dsimp [fiber]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  have hgood : (∑ y ∈ U, (good.filter fun i => f i = y).card) ≤ good.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hsplit : good.card + bad.card = Fintype.card ι := by
    dsimp [good]
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _ : bad ⊆ Finset.univ)
  change bad.card ≤ 2 * (Fintype.card ι - U.card)
  omega

/-- Repeat rank is the number of occurrences minus distinct unpinned slots. -/
theorem repeatRank_add_distinct {α : Type*} [DecidableEq α] (n : ℕ) :
    ∀ (S : Finset α) (ys : Fin n → α),
      repeatRank n S ys + ((Finset.univ.image ys) \ S).card = n := by
  classical
  induction n with
  | zero => intro S ys; simp [repeatRank]
  | succ n ih =>
    intro S ys
    let tail : Fin n → α := fun i => ys i.succ
    have himage : Finset.univ.image ys = insert (ys 0) (Finset.univ.image tail) := by
      ext y
      simp [tail, Fin.exists_fin_succ, eq_comm]
    have hih := ih (insert (ys 0) S) tail
    by_cases hyS : ys 0 ∈ S
    · have hset : insert (ys 0) (Finset.univ.image tail) \ S =
          (Finset.univ.image tail) \ S := by
        ext y
        by_cases heq : y = ys 0
        · subst y; simp [hyS]
        · simp [heq]
      simp only [Finset.insert_eq_of_mem hyS] at hih
      simp only [repeatRank, hyS, ite_true, himage, hset]
      change 1 + repeatRank n (insert (ys 0) S) tail +
        ((Finset.univ.image tail) \ S).card = n + 1
      rw [Finset.insert_eq_of_mem hyS]
      omega
    · let V : Finset α := (Finset.univ.image tail) \ insert (ys 0) S
      have hset : insert (ys 0) (Finset.univ.image tail) \ S = insert (ys 0) V := by
        ext y
        by_cases heq : y = ys 0
        · subst y; simp [V, hyS]
        · simp [V, heq]
      have hyV : ys 0 ∉ V := by simp [V]
      have hcard : (insert (ys 0) V).card = V.card + 1 := Finset.card_insert_of_notMem hyV
      simp only [repeatRank, hyS, ite_false, zero_add, himage, hset, hcard]
      change repeatRank n (insert (ys 0) S) tail + (V.card + 1) = n + 1
      change repeatRank n (insert (ys 0) S) tail + V.card = n at hih
      omega

/-- The occurrence count used for trial pins, expressed using the same rank
as the generating-function estimate. -/
theorem nonunique_occurrences_le_two_repeatRank {α : Type*} [DecidableEq α]
    (n : ℕ) (ys : Fin n → α) (pinned : Finset α) :
    (Finset.univ.filter fun i : Fin n => ys i ∈ pinned ∨
      2 ≤ (Finset.univ.filter fun j : Fin n => ys j = ys i).card).card ≤
      2 * repeatRank n pinned ys := by
  have hcount := nonunique_occurrences_le_two_rank ys pinned
  have hrank := repeatRank_add_distinct n pinned ys
  simp only [Fintype.card_fin] at hcount
  omega

/-- The rank generating function is at most two once its accumulated
collision cost is at most `log 2`. -/
theorem independent_repeat_rank_moment_two {α : Type*} [Fintype α] [DecidableEq α]
    (m n : ℕ) (L a : ℝ) (hL : 0 < L) (ha : 1 ≤ a)
    (P : Fin n → FinLaw α) (S : Finset α) (hS : S.card + n ≤ m)
    (hP : ∀ i y, (P i).w y ≤ 1 / L)
    (hsmall : (n : ℝ) * ((m : ℝ) * a / L) ≤ Real.log 2) :
    (FinLaw.pi P).E (fun ys => a ^ repeatRank n S ys) ≤ 2 := by
  have ha0 : 0 ≤ a := le_trans (by norm_num) ha
  let x : ℝ := (m : ℝ) * a / L
  have hx : 0 ≤ x := by dsimp [x]; positivity
  calc
    _ ≤ (1 + x) ^ n := independent_repeat_rank_moment m L a hL ha n P S hS hP
    _ ≤ (Real.exp x) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      simpa [add_comm] using Real.add_one_le_exp x
    _ = Real.exp ((n : ℝ) * x) := (Real.exp_nat_mul x n).symm
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hsmall
    _ = 2 := Real.exp_log (by norm_num)

/-- Conditional probability for sequential finite sampling. -/
theorem bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α × β → Prop) :
    (FinLaw.bind P K).pr A = P.E (fun a => (K a).pr (fun b => A (a, b))) := by
  classical
  unfold FinLaw.pr FinLaw.E
  simp only [FinLaw.bind]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : A (a, b) <;> simp [hab]

/-- Compatibility and the pinned-list estimate control one sparse-pin trial.
The own-cell draw is averaged only after its valid prior has been identified. -/
theorem compatible_sparse_pin_trial {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (D : ListGateContext κ T k PT)
    (K : ℝ) (hQuant : D.L16QuantitativeValidity K)
    (v : Pos T k) (heven : IsEvenRole v) (pools : D.PoolAssignment)
    (htyp : D.F.typical (D.G.cellOf v) (pools (D.G.cellOf v)))
    (hcompat : D.compatiblePool v pools)
    (pins : Finset (Pos T k)) (hPins : pins ⊆ D.externalEarly v)
    (hcard : pins.card ≤ ListGateContext.pinBudget κ)
    (fixed : Pos T k → Fin (T.S.N k))
    (hperm : ∀ w ∈ pins, fixed w ∈
      D.permittedLabels (D.G.cellOf w) (pools (D.G.cellOf w)) w)
    (hEstimate : ∀ σ : Fin (T.S.N k) → ℝ, D.ValidInitialPrior v σ →
      (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤ D.pinnedPriorMass v σ pins fixed →
      (D.pinnedLabelLaw v pins fixed).pr
        (fun ys => D.gateBad v σ (D.labelsOfPinnedSample v (T.S.N_pos k) ys)) ≤
          Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))) :
    (FinLaw.bind (D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v)))
      (fun _ => D.pinnedLabelLaw v pins fixed)).pr
      (fun ω => D.gateBad v (D.F.prior (D.G.cellOf v) ω.1 v)
        (D.labelsOfPinnedSample v (T.S.N_pos k) ω.2)) ≤
          2 * Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ))) := by
  classical
  let δ : ℝ := Real.rpow (T.S.n k : ℝ) (-(2 * (κ.R : ℝ)))
  have hδ : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let P := D.F.fresh (D.G.cellOf v) (pools (D.G.cellOf v))
  let bad := fun s : D.F.State (D.G.cellOf v) =>
    D.pinnedStatePriorMass v s pins fixed < (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ))
  let g := fun s : D.F.State (D.G.cellOf v) =>
    (D.pinnedLabelLaw v pins fixed).pr
      (fun ys => D.gateBad v (D.F.prior (D.G.cellOf v) s v)
        (D.labelsOfPinnedSample v (T.S.N_pos k) ys))
  have hpoint : ∀ s, P.w s * g s ≤ P.w s * ((if bad s then 1 else 0) + δ) := by
    intro s
    by_cases hz : P.w s = 0
    · simp [hz]
    · have hpos : 0 < P.w s := lt_of_le_of_ne (P.nonneg s) (Ne.symm hz)
      have hsv := D.fresh_spec.fresh_valid (D.G.cellOf v) (pools (D.G.cellOf v)) s htyp hpos
      have hclean := hQuant.prior_shape v (pools (D.G.cellOf v)) s heven htyp hsv
      have hvalid : D.ValidInitialPrior v (D.F.prior (D.G.cellOf v) s v) :=
        ⟨hclean, ⟨pools (D.G.cellOf v), s, htyp, hsv, fun _ => rfl⟩⟩
      apply mul_le_mul_of_nonneg_left _ (P.nonneg s)
      by_cases hbad : bad s
      · have hprob : g s ≤ 1 := pr_le_one _ _
        simpa [hbad] using hprob.trans (by linarith : (1 : ℝ) ≤ 1 + δ)
      · have hmass : (9 / 10 : ℝ) * Real.rpow 2 (-(pins.card : ℝ)) ≤
            D.pinnedPriorMass v (D.F.prior (D.G.cellOf v) s v) pins fixed := by
          rw [Lane_q_s17_pool.pinnedPriorMass_eq_hits D D.tiling_valid v
            (D.F.prior (D.G.cellOf v) s v) hclean pins fixed]
          exact le_of_not_gt hbad
        simpa [hbad, g, δ] using hEstimate (D.F.prior (D.G.cellOf v) s v) hvalid hmass
  have hbad : P.pr bad ≤ δ := hcompat pins hPins hcard fixed hperm
  rw [bind_pr]
  change P.E g ≤ 2 * δ
  calc
    P.E g ≤ ∑ s, P.w s * ((if bad s then 1 else 0) + δ) :=
      Finset.sum_le_sum fun s _ => hpoint s
    _ = P.pr bad + δ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one, one_mul]
      congr 1
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hb : bad s <;> simp [hb]
    _ ≤ δ + δ := by gcongr
    _ = 2 * δ := by ring

/-- A retained row has an exact normalized law, with support and atom growth
controlled by the factor cap and its actual retained mass. -/
theorem normalize_product_row {N n : ℕ} {α : Type*} (μ : Law N)
    (X : Finset (Fin N)) (hμX : μ.SupportedIn X)
    (f : Fin n → Fin N → α → ℝ) (ys : Fin n → α)
    (B C z : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hz : 0 < z)
    (hμB : μ.CapLE B) (hf : ∀ i x, 0 ≤ f i x (ys i))
    (hfC : ∀ i x, f i x (ys i) ≤ C) (hmass : z ≤ productMass μ f ys) :
    ∃ ν : Law N, (∀ x, ν.w x = μ.w x * (∏ i, f i x (ys i)) / productMass μ f ys) ∧
      ν.SupportedIn X ∧ ν.CapLE (B * C ^ n / z) := by
  classical
  let g : Fin N → ℝ := fun x => ∏ i, f i x (ys i)
  have hg : ∀ x, 0 ≤ g x := fun x => Finset.prod_nonneg fun i _ => hf i x
  have hgC : ∀ x, g x ≤ C ^ n := by
    intro x
    calc
      g x ≤ ∏ _i : Fin n, C := Finset.prod_le_prod₀ (fun i _ => hf i x) (fun i _ => hfC i x)
      _ = _ := by simp
  have hZ : 0 < productMass μ f ys := hz.trans_le hmass
  let ν : Law N := Lane_q_s17_pool.reweightLaw μ g hg (productMass μ f ys) hZ rfl
  refine ⟨ν, fun _ => rfl, ?_, ?_⟩
  · intro x hx
    simp [ν, Lane_q_s17_pool.reweightLaw, hμX x hx]
  · intro x
    change (N : ℝ) * (μ.w x * g x / productMass μ f ys) ≤ _
    have hprod : (N : ℝ) * μ.w x * g x ≤ B * C ^ n :=
      mul_le_mul (hμB x) (hgC x) (hg x) hB
    calc
      (N : ℝ) * (μ.w x * g x / productMass μ f ys) =
          ((N : ℝ) * μ.w x * g x) / productMass μ f ys := by ring
      _ ≤ (B * C ^ n) / productMass μ f ys :=
        div_le_div_of_nonneg_right hprod hZ.le
      _ ≤ B * C ^ n / z := div_le_div_of_nonneg_left (by positivity) hz hmass

end HypercubeRamsey.Lane_sol_s17_pool
