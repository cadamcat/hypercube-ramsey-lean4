import HypercubeRamsey.S15.ClusterLabelGeometry_sol_s15_c2
import HypercubeRamsey.S15.ClusterCapacityScales_sol_s15_c2
import HypercubeRamsey.S15.ClusterBinScales_sol_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_prelaw

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

noncomputable def ofProb {Ω : Type*} [Fintype Ω] (P : FinProb Ω) : FinLaw Ω :=
  ⟨P.w, P.nonneg, P.sum_eq_one⟩

lemma pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) : 0 ≤ P.pr A := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs; exact P.nonneg ω; exact le_rfl

lemma pr_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (A : β → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun a => A (f a)) := by
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator, Lane_q_s15_c3.finLaw_map_E,
    ← Lane_sol_s15_transfer.pr_eq_E_indicator]

lemma pr_pi_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (A : ∀ i, Ω i → Prop) :
    (FinLaw.pi P).pr (fun ω => ∀ i, A i (ω i)) = ∏ i, (P i).pr (A i) := by
  classical
  unfold FinLaw.pr FinLaw.pi
  have hprod (ω : ∀ i, Ω i) :
      (if ∀ i, A i (ω i) then ∏ i, (P i).w (ω i) else 0) =
        ∏ i, if A i (ω i) then (P i).w (ω i) else 0 := by
    by_cases h : ∀ i, A i (ω i)
    · simp [h]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [hi]
  simp_rw [hprod]
  exact (Fintype.prod_sum (fun i x => if A i x then (P i).w x else 0)).symm

lemma pr_pi_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (A : Ω i → Prop) :
    (FinLaw.pi P).pr (fun ω => A (ω i)) = (P i).pr A := by
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator,
    Lane_sol_s15_transfer.E_pi_coord P i (fun z => if A z then (1 : ℝ) else 0),
    ← Lane_sol_s15_transfer.pr_eq_E_indicator]

lemma pr_pi_cylinder {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (P : ι → FinLaw β) (S : Finset ι) (o : ι → β) :
    (FinLaw.pi P).pr (fun ω => ∀ i ∈ S, ω i = o i) = ∏ i ∈ S, (P i).w (o i) := by
  classical
  rw [pr_pi_forall P (fun i y => i ∈ S → y = o i)]
  have hterm (i : ι) : (P i).pr (fun y => i ∈ S → y = o i) =
      if i ∈ S then (P i).w (o i) else 1 := by
    by_cases h : i ∈ S
    · simp [FinLaw.pr, h]
    · simp [FinLaw.pr, h, (P i).sum_one]
  simp_rw [hterm]
  rw [← Finset.prod_filter]
  simp

lemma weight_zero_of_pr_zero {Ω : Type*} [Fintype Ω] (P : FinLaw Ω)
    (A : Ω → Prop) (hA : P.pr A = 0) (ω : Ω) (hω : A ω) : P.w ω = 0 := by
  classical
  have hle : P.w ω ≤ P.pr A := by
    unfold FinLaw.pr
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun z => if A z then P.w z else 0)
      (fun z _ => by split_ifs; exact P.nonneg z; exact le_rfl) (Finset.mem_univ ω)
    simpa only [if_pos hω] using h
  exact le_antisymm (hA ▸ hle) (P.nonneg ω)

noncomputable def extendQuery {R β : Type*} [DecidableEq R] [Nonempty β]
    (S : Finset R) (o : S → β) : R → β := fun i =>
  if h : i ∈ S then o ⟨i, h⟩ else Classical.choice (inferInstance : Nonempty β)

lemma expect_partition {δ R β : Type*} [Fintype δ] [Fintype R] [DecidableEq R]
    [Fintype β] [Nonempty β] (L : FinLaw δ) (z : δ → R → β) (S : Finset R)
    (F : (R → β) → ℝ)
    (hdep : ∀ o o', (∀ i ∈ S, o i = o' i) → F o = F o') :
    L.E (fun a => F (z a)) =
      ∑ o : S → β, L.pr (fun a => ∀ i ∈ S, z a i = extendQuery S o i) * F (extendQuery S o) := by
  classical
  unfold FinLaw.E FinLaw.pr
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  let o : S → β := fun i => z a i
  have heq (o' : S → β) : (∀ i ∈ S, z a i = extendQuery S o' i) ↔ o' = o := by
    constructor
    · intro h
      funext i
      have hi' : z a i = o' i := by simpa [extendQuery, o] using h i i.2
      exact hi'.symm
    · rintro rfl i hi
      simp [extendQuery, o, hi]
  simp_rw [heq]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  exact hdep _ _ (by intro i hi; simp [extendQuery, o, hi])

lemma expect_of_cylinders {α γ R β : Type*} [Fintype α] [Fintype γ]
    [Fintype R] [DecidableEq R] [Fintype β] [Nonempty β]
    (P : FinLaw α) (Q : FinLaw γ) (x : α → R → β) (y : γ → R → β)
    (S : Finset R) (C : ℝ)
    (hCyl : ∀ o : R → β, P.pr (fun a => ∀ i ∈ S, x a i = o i) ≤
      C * Q.pr (fun a => ∀ i ∈ S, y a i = o i))
    (F : (R → β) → ℝ) (hF : ∀ o, 0 ≤ F o)
    (hdep : ∀ o o', (∀ i ∈ S, o i = o' i) → F o = F o') :
    P.E (fun a => F (x a)) ≤ C * Q.E (fun a => F (y a)) := by
  classical
  rw [expect_partition P x S F hdep, expect_partition Q y S F hdep, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o _
  calc
    _ ≤ (C * Q.pr (fun a => ∀ i ∈ S, y a i = extendQuery S o i)) * F (extendQuery S o) :=
      mul_le_mul_of_nonneg_right (hCyl (extendQuery S o)) (hF _)
    _ = _ := by ring

noncomputable def blockRead {R V β : Type*} (f : R → V)
    (ω : ∀ v, {i // f i = v} → β) (i : R) : β := ω (f i) ⟨i, rfl⟩

lemma blockRead_eq {R V β : Type*} (f : R → V)
    (ω : ∀ v, {i // f i = v} → β) (i : R) (v : V) (h : f i = v) :
    blockRead f ω i = ω v ⟨i, h⟩ := by
  cases h
  rfl

lemma block_cylinder {R V β : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Fintype β]
    (f : R → V) (J : ∀ v, FinLaw ({i // f i = v} → β))
    (S : Finset R) (o : R → β) :
    (FinLaw.pi J).pr (fun ω => ∀ i ∈ S, blockRead f ω i = o i) =
      ∏ v, (J v).pr (fun z => ∀ i ∈ S.subtype (fun i => f i = v), z i = o i) := by
  classical
  have heq : (fun ω => ∀ i ∈ S, blockRead f ω i = o i) =
      (fun ω => ∀ v, ∀ i ∈ S.subtype (fun i => f i = v), ω v i = o i) := by
    funext ω
    apply propext
    constructor
    · intro h v i hi
      rcases i with ⟨i, hiv⟩
      subst v
      exact h i (by simpa using hi)
    · intro h i hi
      exact h (f i) ⟨i, rfl⟩ (by simpa using hi)
  rw [heq]
  exact pr_pi_forall J (fun v z => ∀ i ∈ S.subtype (fun i => f i = v), z i = o i)

lemma block_cylinder_le {R V β : Type*} [Fintype R] [DecidableEq R]
    [Fintype V] [DecidableEq V] [Fintype β]
    (f : R → V) (p : R → FinLaw β)
    (J : ∀ v, FinLaw ({i // f i = v} → β)) (δ : V → ℝ)
    (S : Finset R) (o : R → β)
    (hJ : ∀ v, (J v).pr (fun z => ∀ i ∈ S.subtype (fun i => f i = v), z i = o i) ≤
      Real.exp (∑ i ∈ S.filter (fun i => f i = v),
        if 2 ≤ (S.filter (fun i => f i = v)).card then δ v else 0) *
        ∏ i ∈ S.filter (fun i => f i = v), (p i).w (o i)) :
    (FinLaw.pi J).pr (fun ω => ∀ i ∈ S, blockRead f ω i = o i) ≤
      Real.exp (∑ i ∈ S, if 2 ≤ (S.filter (fun j => f j = f i)).card then δ (f i) else 0) *
        ∏ i ∈ S, (p i).w (o i) := by
  rw [block_cylinder]
  calc
    _ ≤ ∏ v, (Real.exp (∑ i ∈ S.filter (fun i => f i = v),
        if 2 ≤ (S.filter (fun i => f i = v)).card then δ v else 0) *
        ∏ i ∈ S.filter (fun i => f i = v), (p i).w (o i)) := by
      apply Finset.prod_le_prod₀
      · intro v _; exact pr_nonneg _ _
      · intro v _; exact hJ v
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_fiberwise]
      congr 2
      calc
        _ = ∑ v, ∑ i ∈ S.filter (fun i => f i = v),
            if 2 ≤ (S.filter (fun j => f j = f i)).card then δ (f i) else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = _ := Finset.sum_fiberwise _ _ _

lemma small_atom_scales (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      PT.tiling.mode = .highSmall → ∀ i,
        κ.d0 ≤ (PT.tiling.P i).d ∧ (PT.tiling.P i).d ≤ (T.S.n k) ^ 2 ∧
        2 * Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) /
          (PT.tiling.P i).d ≤ ((PT.tiling.P i).d : ℝ) ^ (-0.95 : ℝ) := by
  let t : ℕ → ℝ := fun k => Real.log (T.S.n k : ℝ)
  let r : ℝ := 4 * κ.ω * (κ.Mhi : ℝ)
  have haC : κ.aC < 1 := by
    have h := hκ.aC_rng.2
    have := min_le_right κ.η0 (1 : ℝ)
    linarith
  have hr0 : 0 < r := by
    have hM : 0 < (κ.Mhi : ℝ) := by nlinarith [hκ.Mhi_big.2, hκ.cq_rng.1]
    dsimp [r]; positivity [hκ.ω_rng.1]
  have hr : r < 0.01 := by
    dsimp [r]
    nlinarith [hκ.ω_rng.1, hκ.ω_rng.2]
  have hω : 4 * κ.ω ≤ 1 := by
    have hM : 1 ≤ (κ.Mhi : ℝ) := by
      have hMlo : (100 : ℝ) < κ.Mlo := by
        have hpos : 0 < 100 * κ.aC / κ.aB := by positivity [hκ.aC_rng.1, hκ.aB_rng.1]
        linarith [hκ.Cb_big, hκ.Mlo_big]
      have hMhi := hκ.Mhi_big.1
      have hpos : 0 < 10 / κ.cq := by positivity [hκ.cq_rng.1]
      linarith
    nlinarith [hκ.ω_rng.1, hκ.ω_rng.2]
  have ht : Tendsto t atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp T.S.n_tendsto)
  have hu : Tendsto (fun k => (t k) ^ κ.cq) atTop atTop :=
    (tendsto_rpow_atTop hκ.cq_rng.1).comp ht
  have hqevent := Lane_sol_consts_adm.eventually_power_sum r 0 1 24 0
    (1.05 * Real.log 2) 0.025 (by linarith) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨Q, hQ⟩ := (eventually_atTop.1 hqevent)
  have htevent := ht.eventually (Lane_sol_consts_adm.eventually_power_sum (2 * r) 0 (1 / 2)
    24 0 (1.05 * Real.log 2) 0.05 (by linarith) (by norm_num) (by norm_num) (by norm_num))
  have ht10 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 10)).comp ht
  filter_upwards [hu.eventually_ge_atTop (max 1 Q), ht.eventually_ge_atTop 1, htevent,
    Lane_sol_s15_c2.high_degree_ge_log_ten κ hκ T,
    ht10.eventually_ge_atTop (κ.d0 : ℝ)] with k hu ht1 htbound hdegree hd0
  intro PT hPT hs i
  let q : ℝ := (PT.tiling.P i).q
  let h : ℝ := (PT.tiling.P i).h
  let d : ℝ := (PT.tiling.P i).d
  rcases hPT.tiling_valid.cluster_data (Or.inr (Or.inl hs)) i with
    ⟨_, _, _, hd, _, _, _, _, hh, _, hsmall, _⟩
  have hqlo : (t k) ^ κ.cq < q := (hsmall.mp hs).1
  have hqhi : q ≤ (t k) ^ (2 : ℕ) := (hsmall.mp hs).2
  have hq1 : 1 ≤ q := (le_max_left _ _).trans (hu.trans hqlo.le)
  have hqQ : Q ≤ q := (le_max_right _ _).trans (hu.trans hqlo.le)
  have hd1 : 1 ≤ d :=
    (Real.one_le_rpow ht1 (by norm_num : (0 : ℝ) ≤ 10)).trans (hdegree PT hPT (Or.inl hs) i)
  have hdpos : 0 < d := by linarith
  have hhUpper : h ≤ 2 * q ^ (κ.Mhi : ℝ) := by simpa [h, q, hs] using hh.le
  have hhpos : 0 < h := by dsimp [h]; exact_mod_cast clusterHeight_pos PT hPT (Or.inl hs) i
  have hh1 : 1 ≤ h := by dsimp [h]; exact_mod_cast Nat.succ_le_iff.mpr (clusterHeight_pos PT hPT (Or.inl hs) i)
  have hK : (PT.tiling.kScale i : ℝ) ≤ 2 * h ^ (3 * κ.ω) := by
    exact Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans
      (Real.one_le_rpow hh1 (by positivity [hκ.ω_rng.1])))
  have hT : (PT.tiling.tScale i : ℝ) ≤ 2 * h ^ κ.ω := by
    exact Nat.ceil_le_two_mul ((by norm_num : (2 : ℝ)⁻¹ ≤ 1).trans
      (Real.one_le_rpow hh1 hκ.ω_rng.1.le))
  have hKT : (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 16 * q ^ r := by
    calc
      _ ≤ (2 * h ^ (3 * κ.ω)) * (2 * h ^ κ.ω) := mul_le_mul hK hT (by positivity) (by positivity)
      _ = 4 * h ^ (4 * κ.ω) := by
        rw [show 4 * κ.ω = 3 * κ.ω + κ.ω by ring, Real.rpow_add hhpos]
        ring
      _ ≤ 4 * (2 * q ^ (κ.Mhi : ℝ)) ^ (4 * κ.ω) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hhpos.le hhUpper (by positivity [hκ.ω_rng.1])) (by norm_num)
      _ = 4 * (2 : ℝ) ^ (4 * κ.ω) * q ^ r := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
          ← Real.rpow_mul (by linarith : 0 ≤ q)]
        dsimp [r]; ring
      _ ≤ 16 * q ^ r := by
        have htwo : (2 : ℝ) ^ (4 * κ.ω) ≤ 2 := by
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hω
        nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ q) r]
  have hqrpow : q ^ r ≤ (t k) ^ (2 * r) := by
    calc
      _ ≤ ((t k) ^ (2 : ℕ)) ^ r := Real.rpow_le_rpow (by linarith : 0 ≤ q) hqhi hr0.le
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ t k)]
        norm_num
  have hqbound : 24 * q ^ r + 1.05 * Real.log 2 ≤ 0.025 * q := by
    simpa only [zero_mul, add_zero, Real.rpow_one] using hQ q hqQ
  have htbound' : 24 * (t k) ^ (2 * r) + 1.05 * Real.log 2 ≤ 0.05 * Real.sqrt (t k) := by
    simpa only [zero_mul, add_zero, Real.sqrt_eq_rpow] using htbound
  let u := min (q / 2) (Real.sqrt (t k))
  have hExpo : Real.log 2 + 1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤
      0.05 * (u - Real.log 2) := by
    have hKTs := mul_le_mul_of_nonneg_left hKT (by norm_num : (0 : ℝ) ≤ 1.5)
    have hq' : 1.05 * Real.log 2 + 1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 0.05 * (q / 2) := by
      linarith only [hKTs, hqbound]
    have ht' : 1.05 * Real.log 2 + 1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 0.05 * Real.sqrt (t k) := by
      nlinarith only [hKTs, htbound', hqrpow]
    have hmin : 1.05 * Real.log 2 + 1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i ≤ 0.05 * u := by
      dsimp [u]; rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 0.05)]
      exact le_min hq' ht'
    linarith only [hmin]
  have hLower : Real.exp u / 2 ≤ d := by
    have hf1 := Nat.lt_floor_add_one (Real.exp (q / 2))
    have hf2 := Nat.lt_floor_add_one (Real.exp (Real.sqrt (t k)))
    have hFormula := hd hs
    have hfloor : Real.exp u < d + 1 := by
      have h1 := (Real.exp_le_exp.mpr (min_le_left (q / 2) (Real.sqrt (t k)))).trans_lt hf1
      have h2 := (Real.exp_le_exp.mpr (min_le_right (q / 2) (Real.sqrt (t k)))).trans_lt hf2
      dsimp [d]
      rw [hFormula, Nat.cast_min]
      by_cases hle : (⌊Real.exp (q / 2)⌋₊ : ℝ) ≤ ⌊Real.exp (Real.sqrt (t k))⌋₊
      · rw [min_eq_left hle]; exact h1
      · rw [min_eq_right (le_of_not_ge hle)]; exact h2
    linarith only [hfloor, hd1]
  have hNumer : 2 * Real.exp (1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) ≤ d ^ (0.05 : ℝ) := by
    calc
      _ = Real.exp (Real.log 2 + 1.5 * (PT.tiling.kScale i : ℝ) * PT.tiling.tScale i) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp (0.05 * (u - Real.log 2)) := Real.exp_le_exp.mpr hExpo
      _ = (Real.exp u / 2) ^ (0.05 : ℝ) := by
        rw [Real.div_rpow (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.exp_mul, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [← Real.exp_sub]
        congr 1; ring
      _ ≤ d ^ (0.05 : ℝ) := Real.rpow_le_rpow (by positivity) hLower (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast hd0.trans (hdegree PT hPT (Or.inl hs) i)
  · have hdUpper : d ≤ Real.exp (Real.sqrt (t k)) := by
      have hnat : (PT.tiling.P i).d ≤ ⌊Real.exp (Real.sqrt (t k))⌋₊ := by rw [hd hs]; exact Nat.min_le_right _ _
      exact (by dsimp [d]; exact_mod_cast hnat : d ≤ (⌊Real.exp (Real.sqrt (t k))⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.exp_pos _).le)
    have hsqrt : Real.sqrt (t k) ≤ 2 * t k := by
      have hs := Real.sqrt_le_sqrt (by nlinarith only [ht1] : t k ≤ (t k) ^ (2 : ℕ))
      rw [Real.sqrt_sq (by linarith : 0 ≤ t k)] at hs
      linarith
    have hexp : Real.exp (2 * t k) = ((T.S.n k : ℝ) ^ (2 : ℕ)) := by
      have hn : 0 < (T.S.n k : ℝ) := by
        have hn1 : 1 < (T.S.n k : ℝ) := (Real.log_pos_iff (by positivity)).mp
          (by change 0 < t k; linarith)
        linarith
      calc
        _ = (Real.exp (t k)) ^ (2 : ℕ) := by
          simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (t k) 2
        _ = _ := by dsimp [t]; rw [Real.exp_log hn]
    have h := hdUpper.trans ((Real.exp_le_exp.mpr hsqrt).trans hexp.le)
    dsimp [d] at h
    exact_mod_cast h
  · calc
      _ ≤ d ^ (0.05 : ℝ) / d := div_le_div_of_nonneg_right hNumer hdpos.le
      _ = d ^ (-0.95 : ℝ) := by
        rw [show (-0.95 : ℝ) = 0.05 - 1 by norm_num, Real.rpow_sub_one hdpos.ne']

lemma sampler_on_set {R : Type} [Fintype R] [DecidableEq R] {N : ℕ}
    (κ : CConsts) (hκ : κ.Admissible) (D : Finset (Fin N))
    (hd : κ.d0 ≤ D.card) (p : R → FinLaw (Fin N))
    (hsupp : ∀ i y, (p i).w y ≠ 0 → y ∈ D)
    (hcap : ∀ i y, (p i).w y ≤ (D.card : ℝ) ^ (-0.95 : ℝ))
    (hload : ∀ y, ∑ i, (p i).w y ≤ 0.4) :
    ∃ J : FinLaw (R → Fin N),
      (∀ ω, J.w ω ≠ 0 → Function.Injective ω) ∧
      (∀ i y, J.pr (fun ω => ω i = y) = (p i).w y) ∧
      (∀ ω, J.w ω ≠ 0 → ∀ i, ω i ∈ D) ∧
      (∀ (S : Finset R) (o : R → Fin N), (S.card : ℝ) ≤ (D.card : ℝ) ^ (0.025 : ℝ) →
        J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
          Real.exp ((D.card : ℝ) ^ (-0.04 : ℝ) * S.card) * ∏ i ∈ S, (p i).w (o i)) := by
  classical
  have hD : 0 < D.card := lt_of_lt_of_le hκ.d0_pos hd
  let e := D.equivFin
  let code : Fin N → Fin D.card := fun y =>
    if hy : y ∈ D then e ⟨y, hy⟩ else ⟨0, hD⟩
  let pp : R → FinProb (Fin N) := fun i => ⟨(p i).w, (p i).nonneg, (p i).sum_one⟩
  have hmarg (i : R) (t : Fin D.card) : labMarg (pp i) code t = (p i).w (e.symm t) := by
    unfold labMarg
    have hterm (y : Fin N) : (if code y = t then (pp i).w y else 0) =
        if y = (e.symm t).val then (p i).w y else 0 := by
      by_cases hy : y ∈ D
      · have he : code y = t ↔ y = (e.symm t).val := by
          simp only [code, dif_pos hy]
          rw [e.apply_eq_iff_eq_symm_apply]
          exact Subtype.ext_iff
        simp only [he]; rfl
      · have hz : (p i).w y = 0 := by by_contra hn; exact hy (hsupp i y hn)
        have hne : y ≠ (e.symm t).val := by intro he; exact hy (he ▸ (e.symm t).2)
        simp [pp, hz, hne]
    simp_rw [hterm]
    simp
  obtain ⟨J, hinj, hsingle, hjoint⟩ := hκ.nearProduct D.card hd (fun _ => code) pp
    (by intro i t; rw [hmarg]; exact hcap i _)
    (by intro t; simp_rw [hmarg]; exact hload _)
  refine ⟨ofProb J, ?_, hsingle, ?_, hjoint⟩
  · intro ω hω i j hij
    exact hinj ω hω (congrArg code hij)
  · intro ω hω i
    by_contra hnot
    have hz : (p i).w (ω i) = 0 := by
      by_contra hne
      exact hnot (hsupp i _ hne)
    have hpr : (ofProb J).pr (fun z => z i = ω i) = 0 := (hsingle i _).trans hz
    exact hω (weight_zero_of_pr_zero _ _ hpr ω rfl)

abbrev PhysicalBin {κ : CConsts} {T : Stage} {k : ℕ} (PT : ProfiledTiling κ T k) :=
  Σ i : Fin PT.tiling.m, Bin PT.tiling i

def physicalSet {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    (v : PhysicalBin PT) : Finset (Fin (T.S.N k)) := v.2.1

lemma physical_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v w : PhysicalBin PT) (hne : v ≠ w) :
    Disjoint (physicalSet v) (physicalSet w) := by
  rcases v with ⟨i, D⟩
  rcases w with ⟨j, D'⟩
  by_cases hij : i = j
  · subst j
    exact (PT.tiling.P i).bins.disjoint D.2 D'.2 (by
      intro h
      apply hne
      congr 1
      exact Subtype.ext h)
  · exact (hPT.tiling_valid.patch_Y_disjoint i j hij).mono
      (Finpartition.le _ D.2) (Finpartition.le _ D'.2)

lemma physicalSet_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) :
    Function.Injective (physicalSet (PT := PT)) := by
  intro v w hvw
  by_contra hne
  obtain ⟨y, hy⟩ := (PT.tiling.P v.1).bins.nonempty_of_mem_parts v.2.2
  exact Finset.disjoint_left.mp (physical_disjoint PT hPT v w hne) hy (hvw ▸ hy)

noncomputable def binAt {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (b : OddPosition T k) : PhysicalBin PT :=
  ⟨patchAt PT hPT b.1, B (clusterGroupIndexAt PT hPT hm b)⟩

lemma binAt_eq_iff {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (b c : OddPosition T k) :
    binAt PT hPT hm B b = binAt PT hPT hm B c ↔
      (B (clusterGroupIndexAt PT hPT hm b)).1 = (B (clusterGroupIndexAt PT hPT hm c)).1 :=
  ⟨congrArg physicalSet, by intro h; apply physicalSet_injective PT hPT; exact h⟩

lemma bin_count_eq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (S : Finset (OddPosition T k)) (b : OddPosition T k) :
    (S.filter fun c => binAt PT hPT hm B c = binAt PT hPT hm B b).card =
      clusterBinQueryCount PT hPT hm B S b := by
  unfold clusterBinQueryCount
  congr 1
  ext c
  simp only [Finset.mem_filter, binAt_eq_iff]

noncomputable def internalOfOdds {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : OddPosition T k → Fin (T.S.N k)) : ClusterInternalData PT :=
  Lane_sol_s15_transfer.internalOfWordLabels B (fun c =>
    if hc : ∃ b, Lane_sol_s15_transfer.wordAtOdd PT hPT hm b = c then ys (Classical.choose hc)
    else ⟨0, T.S.N_pos k⟩)

lemma internalOfOdds_label {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : OddPosition T k → Fin (T.S.N k)) (b : OddPosition T k) :
    clusterLabelFromInternal (hPT := hPT) hm (internalOfOdds PT hPT hm B ys) b = ys b := by
  have hc : ∃ b', Lane_sol_s15_transfer.wordAtOdd PT hPT hm b' =
      Lane_sol_s15_transfer.wordAtOdd PT hPT hm b := ⟨b, rfl⟩
  change (if h : ∃ b', Lane_sol_s15_transfer.wordAtOdd PT hPT hm b' =
      Lane_sol_s15_transfer.wordAtOdd PT hPT hm b then ys (Classical.choose h) else _) = _
  rw [dif_pos hc]
  congr 1
  exact Lane_sol_s15_c2.wordAtOdd_injective PT hPT hm (Classical.choose_spec hc)

lemma internalOfOdds_pins {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (B : ClusterBinAssignment PT) (ys : OddPosition T k → Fin (T.S.N k)) :
    clusterBinsOfInternal (internalOfOdds PT hPT hm B ys) = B := rfl

lemma independent_cylinder {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (S : Finset (OddPosition T k)) (o : OddPosition T k → Fin (T.S.N k)) :
    (clusterIndependentLabelKernel PT hPT hm W B).pr
      (fun I => ∀ b ∈ S, clusterLabelFromInternal (hPT := hPT) hm I b = o b) =
      ∏ b ∈ S, (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w (o b) := by
  classical
  let f := Lane_sol_s15_transfer.wordAtOdd PT hPT hm
  let oy : ClusterConsultation PT → Fin (T.S.N k) := fun c =>
    if hc : ∃ b, f b = c then o (Classical.choose hc) else ⟨0, T.S.N_pos k⟩
  have hoy (b : OddPosition T k) : oy (f b) = o b := by
    have hc : ∃ b', f b' = f b := ⟨b, rfl⟩
    simp only [oy, dif_pos hc]
    congr 1
    exact Lane_sol_s15_c2.wordAtOdd_injective PT hPT hm (Classical.choose_spec hc)
  rw [Lane_sol_s15_transfer.pr_eq_E_indicator, Lane_sol_s15_transfer.independent_label_E_eq_word_E,
    ← Lane_sol_s15_transfer.pr_eq_E_indicator]
  have heq : (fun ys => ∀ b ∈ S, clusterLabelFromInternal (hPT := hPT) hm
      (Lane_sol_s15_transfer.internalOfWordLabels B ys) b = o b) =
      (fun ys => ∀ c ∈ S.image f, ys c = oy c) := by
    funext ys
    apply propext
    constructor
    · intro h c hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      rw [hoy]
      exact h b hb
    · intro h b hb
      exact (h (f b) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)).trans (hoy b)
  rw [heq, pr_pi_cylinder, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro b hb
    rw [hoy]
    rfl
  · exact (Lane_sol_s15_c2.wordAtOdd_injective PT hPT hm).injOn

lemma cylinder_exact_error {R β : Type*} [Fintype R] [DecidableEq R] [Fintype β]
    (J : FinLaw (R → β)) (p : R → FinLaw β) (δ : ℝ)
    (hSingle : ∀ i y, J.pr (fun ω => ω i = y) = (p i).w y)
    (S : Finset R) (o : R → β)
    (hJoint : J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
      Real.exp (δ * S.card) * ∏ i ∈ S, (p i).w (o i)) :
    J.pr (fun ω => ∀ i ∈ S, ω i = o i) ≤
      Real.exp (∑ _i ∈ S, if 2 ≤ S.card then δ else 0) * ∏ i ∈ S, (p i).w (o i) := by
  classical
  by_cases htwo : 2 ≤ S.card
  · simpa [htwo, mul_comm] using hJoint
  · have hc : S.card = 0 ∨ S.card = 1 := by omega
    rcases hc with h0 | h1
    · have hS := Finset.card_eq_zero.mp h0
      subst S
      simp [FinLaw.pr, J.sum_one]
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      simpa using le_of_eq (hSingle i (o i))

lemma role_count_le {R : Type*} [Fintype R] {N : ℕ}
    (D : Finset (Fin N)) (p : R → FinLaw (Fin N))
    (hsupp : ∀ i y, (p i).w y ≠ 0 → y ∈ D)
    (hload : ∀ y, ∑ i, (p i).w y ≤ 0.4) : (Fintype.card R : ℝ) ≤ D.card := by
  classical
  have hrow (i : R) : ∑ y ∈ D, (p i).w y = 1 := by
    rw [← (p i).sum_one]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    by_contra hn
    exact hy (hsupp i y hn)
  calc
    (Fintype.card R : ℝ) = ∑ i : R, ∑ y ∈ D, (p i).w y := by simp_rw [hrow]; simp
    _ = ∑ y ∈ D, ∑ i : R, (p i).w y := Finset.sum_comm
    _ ≤ ∑ _y ∈ D, (0.4 : ℝ) := Finset.sum_le_sum fun y _ => hload y
    _ ≤ D.card := by simp only [Finset.sum_const, nsmul_eq_mul]; nlinarith [(Nat.cast_nonneg D.card : (0 : ℝ) ≤ (D.card : ℝ))]

lemma small_bin_samplers (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
    ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
    PT.tiling.mode = .highSmall →
    ∀ W : ClusterHistory PT hPT hm, ∀ B : ClusterBinAssignment PT,
    0 < (clusterIndependentBinKernel PT hPT hm W).w B → clusterBinGood PT hPT hm W B →
    ∃ Q : ∀ v : PhysicalBin PT,
      FinLaw ({b : OddPosition T k // binAt PT hPT hm B b = v} → Fin (T.S.N k)),
    ∀ v,
      (∀ ω, (Q v).w ω ≠ 0 → Function.Injective ω) ∧
      (∀ b y, (Q v).pr (fun ω => ω b = y) =
        (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w y) ∧
      (∀ ω, (Q v).w ω ≠ 0 → ∀ b, ω b ∈ physicalSet v) ∧
      (∀ (S : Finset {b : OddPosition T k // binAt PT hPT hm B b = v})
        (o : {b : OddPosition T k // binAt PT hPT hm B b = v} → Fin (T.S.N k)),
        (S.card : ℝ) ≤ ((physicalSet v).card : ℝ) ^ (0.025 : ℝ) →
        (Q v).pr (fun ω => ∀ b ∈ S, ω b = o b) ≤
          Real.exp (((physicalSet v).card : ℝ) ^ (-0.04 : ℝ) * S.card) *
            ∏ b ∈ S, (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w (o b)) ∧
      ((Finset.univ.filter fun b => binAt PT hPT hm B b = v).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
  filter_upwards [small_atom_scales κ hκ T] with k hscale
  intro PT hPT hm hs W B hB hgood
  let f := binAt PT hPT hm B
  let p := Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B
  have hq (g : ClusterGroupIndex PT) :
      0 < (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g) := by
    have hn : (clusterIndependentBinKernel PT hPT hm W).w B ≠ 0 := hB.ne'
    change (∏ g : ClusterGroupIndex PT, (clusterSolver PT hPT hm g.1.1).q g.2 (historyOnSlice W g.1) (B g)) ≠ 0 at hn
    exact lt_of_le_of_ne ((clusterSolver PT hPT hm g.1.1).q_nonneg _ _ _) (Ne.symm
      (Finset.prod_ne_zero_iff.mp hn g (Finset.mem_univ g)))
  have hdata (v : PhysicalBin PT) : ∃ J : FinLaw ({b : OddPosition T k // f b = v} → Fin (T.S.N k)),
      (∀ ω, J.w ω ≠ 0 → Function.Injective ω) ∧
      (∀ b y, J.pr (fun ω => ω b = y) = (p b).w y) ∧
      (∀ ω, J.w ω ≠ 0 → ∀ b, ω b ∈ physicalSet v) ∧
      (∀ (S : Finset {b : OddPosition T k // f b = v})
        (o : {b : OddPosition T k // f b = v} → Fin (T.S.N k)),
        (S.card : ℝ) ≤ ((physicalSet v).card : ℝ) ^ (0.025 : ℝ) →
        J.pr (fun ω => ∀ b ∈ S, ω b = o b) ≤
          Real.exp (((physicalSet v).card : ℝ) ^ (-0.04 : ℝ) * S.card) *
            ∏ b ∈ S, (p b).w (o b)) ∧
      ((Finset.univ.filter fun b => f b = v).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
    have hDcard : (physicalSet v).card = (PT.tiling.P v.1).d :=
      hPT.tiling_valid.bins_card v.1 v.2.1 v.2.2
    have hsupp (b : {b : OddPosition T k // f b = v}) (y) (hy : (p b).w y ≠ 0) : y ∈ physicalSet v := by
      have h := (clusterSolver PT hPT hm (patchAt PT hPT b.1.1)).U_support
        (clusterGroupIndexAt PT hPT hm b).2 (historyOnSlice W (clusterSliceAt PT hPT b.1.1))
        (B (clusterGroupIndexAt PT hPT hm b)) y hy
      change y ∈ physicalSet (f b) at h
      rw [b.2] at h
      exact h
    have hcap (b : {b : OddPosition T k // f b = v}) (y) :
        (p b).w y ≤ ((physicalSet v).card : ℝ) ^ (-0.95 : ℝ) := by
      have hi : patchAt PT hPT b.1.1 = v.1 := congrArg Sigma.fst b.2
      have h := (clusterSolver PT hPT hm (patchAt PT hPT b.1.1)).U_atom_cap
        (clusterGroupIndexAt PT hPT hm b).2 (historyOnSlice W (clusterSliceAt PT hPT b.1.1))
        (B (clusterGroupIndexAt PT hPT hm b)) y (hq (clusterGroupIndexAt PT hPT hm b))
      have h' := h.trans (hscale PT hPT hs (patchAt PT hPT b.1.1)).2.2
      change (p b).w y ≤ ((PT.tiling.P (patchAt PT hPT b.1.1)).d : ℝ) ^ (-0.95 : ℝ) at h'
      rw [hi] at h'
      rw [hDcard]
      exact h'
    have hload (y) : ∑ b : {b : OddPosition T k // f b = v}, (p b).w y ≤ 0.4 := by
      rw [← Finset.sum_subtype (Finset.univ.filter fun b => f b = v) (by intro b; simp)
        (fun b => (p b).w y)]
      calc
        _ ≤ ∑ b : OddPosition T k, (p b).w y := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun b _ _ => (p b).nonneg y)
        _ ≤ clusterGivenBinColumn PT hPT hm W B y := Lane_sol_s15_c2.odd_label_column_le PT hPT hm W B y
        _ ≤ κ.θ0 := hgood.2.1 y
        _ ≤ 0.4 := by rw [hκ.clock.2.1]; norm_num
    obtain ⟨J, hinj, hsingle, hJsupport, hjoint⟩ := sampler_on_set κ hκ (physicalSet v)
      (by rw [hDcard]; exact (hscale PT hPT hs v.1).1) (fun b : {b : OddPosition T k // f b = v} => p b)
      hsupp hcap hload
    refine ⟨J, hinj, hsingle, hJsupport, hjoint, ?_⟩
    have hc := role_count_le (physicalSet v) (fun b : {b : OddPosition T k // f b = v} => p b) hsupp hload
    have hcount : Fintype.card {b : OddPosition T k // f b = v} =
        (Finset.univ.filter fun b => f b = v).card := Fintype.card_subtype _
    rw [hcount] at hc
    exact hc.trans (by rw [hDcard]; exact_mod_cast (hscale PT hPT hs v.1).2.1)
  choose Q hQ using hdata
  exact ⟨Q, hQ⟩


lemma product_preComparison {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (hs : PT.tiling.mode = .highSmall)
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (Q : ∀ v : PhysicalBin PT,
      FinLaw ({b : OddPosition T k // binAt PT hPT hm B b = v} → Fin (T.S.N k)))
    (hSingle : ∀ v b y, (Q v).pr (fun z => z b = y) =
      (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w y)
    (hJoint : ∀ v (S : Finset {b : OddPosition T k // binAt PT hPT hm B b = v})
      (o : {b : OddPosition T k // binAt PT hPT hm B b = v} → Fin (T.S.N k)),
      (S.card : ℝ) ≤ ((physicalSet v).card : ℝ) ^ (0.025 : ℝ) →
      (Q v).pr (fun z => ∀ b ∈ S, z b = o b) ≤
        Real.exp (((physicalSet v).card : ℝ) ^ (-0.04 : ℝ) * S.card) *
          ∏ b ∈ S, (Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B b).w (o b))
    (F : ClusterInternalData PT → ℝ) (hF : ∀ I, 0 ≤ F I)
    (S : Finset (OddPosition T k)) (hdep : ClusterLabelDependsOn hPT hm F S)
    (hquery : ClusterLabelQueryOK PT hPT hm B S) :
    (FinLaw.map (FinLaw.pi Q) (fun ω => internalOfOdds PT hPT hm B
      (blockRead (binAt PT hPT hm B) ω))).E F ≤
      clusterLabelError PT hPT hm B S * (clusterIndependentLabelKernel PT hPT hm W B).E F := by
  classical
  let f := binAt PT hPT hm B
  let p := Lane_sol_s15_c2.oddLabelLaw PT hPT hm W B
  let δ := fun v : PhysicalBin PT =>
    ((physicalSet v).card : ℝ) ^ (-0.04 : ℝ)
  have hCyl (o : OddPosition T k → Fin (T.S.N k)) :
      (FinLaw.pi Q).pr (fun ω => ∀ b ∈ S, blockRead f ω b = o b) ≤
        clusterLabelError PT hPT hm B S * (clusterIndependentLabelKernel PT hPT hm W B).pr
          (fun I => ∀ b ∈ S, clusterLabelFromInternal (hPT := hPT) hm I b = o b) := by
    have hbound := block_cylinder_le f p Q δ S o
    have hlocal (v : PhysicalBin PT) :
        (Q v).pr (fun z => ∀ b ∈ S.subtype (fun b => f b = v), z b = o b) ≤
          Real.exp (∑ b ∈ S.filter (fun b => f b = v),
            if 2 ≤ (S.filter (fun b => f b = v)).card then δ v else 0) *
            ∏ b ∈ S.filter (fun b => f b = v), (p b).w (o b) := by
      have hsize : ((S.subtype (fun b => f b = v)).card : ℝ) ≤
          ((physicalSet v).card : ℝ) ^ (0.025 : ℝ) := by
        by_cases hempty : (S.subtype (fun b => f b = v)).Nonempty
        · obtain ⟨b, hb⟩ := hempty
          have hbs : b.1 ∈ S := by simpa using hb
          have hqueryb := hquery hs b hbs
          have hfilter : (S.filter fun c => f c = v).card =
              clusterBinQueryCount PT hPT hm B S b := by
            have h := bin_count_eq PT hPT hm B S b.1
            change (S.filter fun c => f c = f b.1).card = _ at h
            simpa only [b.2] using h
          rw [Finset.card_subtype, hfilter]
          have hcardbin : (physicalSet v).card =
              (PT.tiling.P (patchAt PT hPT b.1.1)).d := by
            have h : (physicalSet (f b.1)).card =
                (PT.tiling.P (patchAt PT hPT b.1.1)).d :=
              hPT.tiling_valid.bins_card _ _ (B (clusterGroupIndexAt PT hPT hm b)).2
            simpa only [b.2] using h
          rw [hcardbin]
          exact hqueryb
        · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
          simp only [Finset.card_empty, Nat.cast_zero]
          exact Real.rpow_nonneg (by positivity) _
      have hj := hJoint v (S.subtype (fun b => f b = v)) (fun b => o b) hsize
      have hexact := cylinder_exact_error (Q v)
        (fun b : {b : OddPosition T k // f b = v} => p b) (δ v)
        (hSingle v) (S.subtype (fun b => f b = v)) (fun b => o b) hj
      rw [Finset.card_subtype,
        Finset.sum_subtype_eq_sum_filter (s := S) (p := fun b => f b = v)
          (fun _ : OddPosition T k => if 2 ≤ (S.filter fun b => f b = v).card then δ v else 0),
        Finset.prod_subtype_eq_prod_filter (s := S) (p := fun b => f b = v)
          (fun b : OddPosition T k => (p b).w (o b))] at hexact
      exact hexact
    have h := hbound hlocal
    have herr : Real.exp (∑ b ∈ S, if 2 ≤ (S.filter fun c => f c = f b).card then δ (f b) else 0) =
        clusterLabelError PT hPT hm B S := by
      rw [clusterLabelError, if_pos hs]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [bin_count_eq]
      have hdb : (physicalSet (f b)).card =
          (PT.tiling.P (patchAt PT hPT b.1)).d :=
        hPT.tiling_valid.bins_card _ _ (B (clusterGroupIndexAt PT hPT hm b)).2
      simp only [δ, hdb]
    rw [herr, ← independent_cylinder PT hPT hm W B S o] at h
    exact h
  let G := fun ys : OddPosition T k → Fin (T.S.N k) =>
    F (internalOfOdds PT hPT hm B ys)
  have hGdep : ∀ ys ys', (∀ b ∈ S, ys b = ys' b) → G ys = G ys' := by
    intro ys ys' heq
    apply hdep
    intro b hb
    simp only [internalOfOdds_label]
    exact heq b hb
  letI : Nonempty (Fin (T.S.N k)) := ⟨⟨0, T.S.N_pos k⟩⟩
  have hE := expect_of_cylinders (FinLaw.pi Q)
    (clusterIndependentLabelKernel PT hPT hm W B) (blockRead f)
    (fun I => clusterLabelFromInternal (hPT := hPT) hm I) S
    (clusterLabelError PT hPT hm B S) hCyl G (fun ys => hF _) hGdep
  rw [Lane_q_s15_c3.finLaw_map_E]
  have heq (I : ClusterInternalData PT) :
      G (clusterLabelFromInternal (hPT := hPT) hm I) = F I := by
    apply hdep
    intro b hb
    exact internalOfOdds_label PT hPT hm B _ b
  simpa only [heq] using hE

end HypercubeRamsey.Lane_sol_s15_prelaw
