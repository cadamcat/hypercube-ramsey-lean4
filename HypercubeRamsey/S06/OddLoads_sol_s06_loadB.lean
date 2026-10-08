import HypercubeRamsey.S06.OddLoads_q_s06_loads

namespace HypercubeRamsey.Lane_sol_s06_loadB
open S06 OAI.HypercubeRamsey
open scoped BigOperators
set_option maxHeartbeats 1000000
noncomputable section

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop}
  {G : Colour} {M : TagMix N}

/-- The finite avoidance set is the event used by the third stage. -/
theorem mem_avoid_bad3 (X : Ctx6 γ p₀ K n N E G M) (b : X.Base) (Z : X.Hid) :
    Z ∈ LocalLemma.avoid (X.bad3Set b) Finset.univ ↔ ∀ gr, ¬ X.Bad3 b gr Z := by
  classical
  simp [LocalLemma.avoid, Ctx6.bad3Set]

/-- Convert the weighted avoidance estimate to the actual stage law. -/
theorem stage3_compare_local (X : Ctx6 γ p₀ K n N E G M) (b : X.Base)
    (xmax : ℝ) (cert : AvoidCert6 (X.hidLaw b).w (X.bad3Set b) xmax)
    (hx : xmax < 1) (U : Finset X.HKey) (W : X.Hid → ℝ)
    (hW : FinProb.DependsOn W U) (hW0 : ∀ Z, 0 ≤ W Z)
    (S T : Finset (X.Bin × CubeVertex X.m)) (hST : Disjoint S T)
    (hUnion : S ∪ T = Finset.univ)
    (hS : ∀ gr ∈ S, Disjoint U (Lane_q_s06_loads.bad3HidScope6 X gr)) :
    (X.stage3Law b).expect W ≤ (∏ gr ∈ T, (1 - cert.x gr)⁻¹) *
      (X.hidLaw b).expect W := by
  classical
  let q : X.HKey → Fin N → ℝ := fun ℓ => (X.hidPost b ℓ.1).w
  have hq0 : ∀ ℓ a, 0 ≤ q ℓ a := fun ℓ a => (X.hidPost b ℓ.1).nonneg a
  have hq1 : ∀ ℓ, ∑ a, q ℓ a = 1 := fun ℓ => (X.hidPost b ℓ.1).sum_eq_one
  have hscope : ∀ gr (Z Z' : X.Hid),
      (∀ ℓ ∈ Lane_q_s06_loads.bad3HidScope6 X gr, Z ℓ = Z' ℓ) →
      (Z ∈ X.bad3Set b gr ↔ Z' ∈ X.bad3Set b gr) := by
    intro gr Z Z' heq
    simpa [Ctx6.bad3Set] using
      _root_.Lane_q_s06_loads.bad3_congr_hidScope X b gr Z Z' heq
  have hpos := Lane_q_s06_loads.S06.AvoidCert6.mass_avoid_pos cert
    (X.hidLaw b).nonneg (X.hidLaw b).sum_eq_one hx
  have hmass : LocalLemma.mass (X.hidLaw b).w
      (LocalLemma.avoid (X.bad3Set b) Finset.univ) =
      (X.hidLaw b).pr (fun Z => ∀ gr, ¬ X.Bad3 b gr Z) := by
    unfold LocalLemma.mass FinProb.pr
    rw [← Finset.sum_ite_mem_eq]
    apply Finset.sum_congr rfl
    intro Z _
    by_cases hg : ∀ gr, ¬ X.Bad3 b gr Z
    · simp [mem_avoid_bad3, hg]
    · simp [mem_avoid_bad3, hg]
  have hnum : (∑ Z ∈ LocalLemma.avoid (X.bad3Set b) Finset.univ,
        (X.hidLaw b).w Z * W Z) =
      ∑ Z, if (∀ gr, ¬ X.Bad3 b gr Z) then (X.hidLaw b).w Z * W Z else 0 := by
    rw [← Finset.sum_ite_mem_eq]
    apply Finset.sum_congr rfl
    intro Z _
    by_cases hg : ∀ gr, ¬ X.Bad3 b gr Z
    · simp [mem_avoid_bad3, hg]
    · simp [mem_avoid_bad3, hg]
  have hfactor : (∑ Z ∈ LocalLemma.avoid (X.bad3Set b) S,
      (X.hidLaw b).w Z * W Z) = (X.hidLaw b).expect W *
        LocalLemma.mass (X.hidLaw b).w (LocalLemma.avoid (X.bad3Set b) S) := by
    simpa only [q, Ctx6.hidLaw, FinProb.pi, FinProb.expect] using
      _root_.Lane_q_s06_loads.product_weight_avoid_factor
        q hq0 hq1 (X.bad3Set b) (Lane_q_s06_loads.bad3HidScope6 X) hscope U W hW S hS
  have hposS := _root_.Lane_q_s06_loads.avoid_mass_positive_subset cert
    (X.hidLaw b).nonneg (X.hidLaw b).sum_eq_one hx S
  have hratio : (∑ Z ∈ LocalLemma.avoid (X.bad3Set b) S,
      (X.hidLaw b).w Z * W Z) /
      LocalLemma.mass (X.hidLaw b).w (LocalLemma.avoid (X.bad3Set b) S) =
        (X.hidLaw b).expect W := by
    rw [hfactor]
    exact mul_div_cancel_right₀ _ (ne_of_gt hposS)
  let p : (X.Bin × CubeVertex X.m) → ℝ := fun gr => cert.x gr *
    ∏ gr' ∈ Finset.univ.filter (cert.adj gr), (1 - cert.x gr')
  have havoid := LocalLemma.conditional_avoidance (X.hidLaw b).w
    (X.hidLaw b).nonneg (X.hidLaw b).sum_eq_one (X.bad3Set b) cert.adj
    cert.adj_symm cert.adj_irrefl p cert.x cert.local_bound cert.x_nonneg
    (fun gr => (cert.x_le gr).trans_lt hx) (fun _ => le_rfl)
  have hcompare := havoid.2.2.1 S T hST W hW0
  rw [hUnion, hratio, ← Finset.prod_inv_distrib] at hcompare
  rw [Lane_q_s06_loads.stage3Law_expect_formula X b (by rwa [← hmass]) W]
  rw [← hnum, ← hmass]
  exact hcompare

/-- Stage-3 products of functions on disjoint small scopes cost a factor two per function. -/
theorem stage3_local_joint (X : Ctx6 γ p₀ K n N E G M) (b : X.Base)
    (cert : AvoidCert6 (X.hidLaw b).w (X.bad3Set b) ((n : ℝ) ^ (-(δ₂ / 128))))
    (hsmall : 2 * (n : ℝ) ^ (-(δ₂ / 128)) *
      (602 ^ 8 * (9 * (X.m + 1) ^ 8) : ℝ) ≤ Real.log 2)
    (U : Finset (CubeVertex n)) (f : CubeVertex n → X.Hid → ℝ)
    (hf : ∀ u, FinProb.DependsOn (f u) (Lane_q_s06_loads.proxyHidScope6 X u))
    (hf0 : ∀ u Z, 0 ≤ f u Z)
    (hdis : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → Disjoint
      (Lane_q_s06_loads.proxyHidScope6 X u) (Lane_q_s06_loads.proxyHidScope6 X u')) :
    (X.stage3Law b).expect (fun Z => ∏ u ∈ U, f u Z) ≤
      (2 : ℝ) ^ U.card * ∏ u ∈ U, (X.hidLaw b).expect (f u) := by
  classical
  let xmax : ℝ := (n : ℝ) ^ (-(δ₂ / 128))
  let B : ℕ := 602 ^ 8 * (9 * (X.m + 1) ^ 8)
  have hBcast : (B : ℝ) = 602 ^ 8 * (9 * (X.m + 1) ^ 8) := by
    dsimp [B]
    push_cast
    norm_num
  rw [← hBcast] at hsmall
  change 2 * xmax * (B : ℝ) ≤ Real.log 2 at hsmall
  have hx0 : 0 ≤ xmax := by dsimp [xmax]; positivity
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by
    have hBp : 0 < B := by dsimp [B]; positivity
    exact_mod_cast Nat.succ_le_of_lt hBp
  have hxhalf : xmax ≤ 1 / 2 := by
    have hm : 2 * xmax ≤ 2 * xmax * (B : ℝ) :=
      le_mul_of_one_le_right (by positivity) hB1
    have hlog : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    linarith
  let Uscope := _root_.Lane_q_s06_loads.proxyHidScopeUnion6 X U
  let W : X.Hid → ℝ := fun Z => ∏ u ∈ U, f u Z
  have hW : FinProb.DependsOn W Uscope := by
    intro Z Z' heq
    apply Finset.prod_congr rfl
    intro u hu
    apply hf u
    intro ℓ hℓ
    exact heq ℓ (Finset.mem_biUnion.mpr ⟨u, hu, hℓ⟩)
  have hW0 : ∀ Z, 0 ≤ W Z := fun Z => Finset.prod_nonneg fun u _ => hf0 u Z
  let T := _root_.Lane_q_s06_loads.bad3GroupsTouchProxyUnion6 X U
  let S := Finset.univ \ T
  have hST : Disjoint S T := Finset.sdiff_disjoint
  have hUnion : S ∪ T = Finset.univ := by ext gr; simp [S]
  have hS : ∀ gr ∈ S, Disjoint Uscope (Lane_q_s06_loads.bad3HidScope6 X gr) := by
    intro gr hgr
    have hnot := (Finset.mem_sdiff.mp hgr).2
    by_contra hd
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)
  have hcompare := stage3_compare_local X b xmax cert (by linarith) Uscope W hW hW0
    S T hST hUnion hS
  have hcharge : (∏ gr ∈ T, (1 - cert.x gr)⁻¹) ≤ (2 : ℝ) ^ U.card := by
    apply _root_.Lane_q_s06_loads.avoidance_charge_product_le_two_pow
      T cert.x xmax U.card B hx0 hxhalf
    · intro gr
      exact ⟨cert.x_nonneg gr, cert.x_le gr⟩
    · exact _root_.Lane_q_s06_loads.bad3GroupsTouchProxyUnion6_card_le X U
    · exact hsmall
  have hraw0 : 0 ≤ (X.hidLaw b).expect W := by
    unfold FinProb.expect
    exact Finset.sum_nonneg fun Z _ => mul_nonneg ((X.hidLaw b).nonneg Z) (hW0 Z)
  have hfactor : (X.hidLaw b).expect W = ∏ u ∈ U, (X.hidLaw b).expect (f u) := by
    exact _root_.Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint
      (fun ℓ : X.HKey => X.hidPost b ℓ.1) U
      (Lane_q_s06_loads.proxyHidScope6 X) f hf hdis
  exact hcompare.trans ((mul_le_mul_of_nonneg_right hcharge hraw0).trans_eq
    (by rw [hfactor]))

/-- An even type reads only the radius-four scope at its role. -/
theorem evenType_obs_subset (X : Ctx6 γ p₀ K n N E G M) (x : CubeVertex n) :
    (X.evenType x).obs ⊆ Lane_q_s06_loads.proxyHidScope6 X x := by
  classical
  intro ℓ hℓ
  have hg := _root_.Lane_q_s06_loads.makeType6_obs_scope binAdjacent6
    (X.g.L.key x) (X.g.L.sign x) (X.g.L.flippable x) (X.g.L.severity x) X.J ℓ
    (by simpa [Ctx6.evenType] using hℓ)
  have hk1 : ℓ.1 ∈ Lane_q_s06_loads.keyBall6 X (X.g.L.key x) 1 := by
    rcases hg.1 with heq | hc
    · rw [heq]
      exact Lane_q_s06_loads.keyBall6_contains_root X _ 1
    · exact _root_.Lane_q_s06_loads.keyBall6_extend_C X _ _ _ 0
        (by simp [Lane_q_s06_loads.keyBall6]) hc
  have hk2 := _root_.Lane_q_s06_loads.keyBall6_pad_self X _ _ 1 hk1
  have hk3 := _root_.Lane_q_s06_loads.keyBall6_pad_self X _ _ 2 hk2
  have hk4 := _root_.Lane_q_s06_loads.keyBall6_pad_self X _ _ 3 hk3
  apply Finset.mem_product.mpr
  exact ⟨hk4, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg.2.trans (by omega)⟩⟩

/-- All even Step-2 caps fit the subexponential cap used for sign moments. -/
theorem even_cap_eventually (α K : ℝ) (hα : 0 < α) (hK : 0 < K) :
    ∃ m₀ : ℕ, ∀ n m : ℕ, m₀ ≤ m → 1 ≤ n → (n : ℝ) ^ α ≤ (m : ℝ) →
      K * (n : ℝ) ^ (d₂ * (Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) + 1)) ≤
        Real.exp ((m : ℝ) ^ (15 / 100 : ℝ)) := by
  have hlog : ∀ᶠ m : ℕ in Filter.atTop,
      Real.log (m : ℝ) ≤ (m : ℝ) ^ (5 / 100 : ℝ) := by
    have hh := ((isLittleO_log_rpow_atTop
      (by norm_num : (0 : ℝ) < 5 / 100)).comp_tendsto
      tendsto_natCast_atTop_atTop).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh] with m hm
    have hm' : |Real.log (m : ℝ)| ≤ (m : ℝ) ^ (5 / 100 : ℝ) := by
      simpa only [Function.comp_apply, Real.norm_eq_abs, one_mul, abs_of_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg m) _)] using hm
    exact (le_abs_self _).trans hm'
  have hp09 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 100)).comp
    tendsto_natCast_atTop_atTop
  have hp06 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 6 / 100)).comp
    tendsto_natCast_atTop_atTop
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1
    ((Filter.eventually_ge_atTop (1 : ℕ)).and (hlog.and
      ((hp09.eventually (Filter.eventually_ge_atTop (Real.log K))).and
        (hp06.eventually (Filter.eventually_ge_atTop (1 + 2 * d₂ / α))))))
  refine ⟨m₀, ?_⟩
  intro n m hm hn hnm
  obtain ⟨hm1, hlogm, hlogK, hgrowth⟩ := hm₀ m hm
  change Real.log K ≤ (m : ℝ) ^ (9 / 100 : ℝ) at hlogK
  change 1 + 2 * d₂ / α ≤ (m : ℝ) ^ (6 / 100 : ℝ) at hgrowth
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmp : 0 < (m : ℝ) := by positivity
  have hnp : 0 < (n : ℝ) := by positivity
  have hlogn : Real.log (n : ℝ) ≤ Real.log (m : ℝ) / α := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hnp α) hnm
    rw [Real.log_rpow hnp] at h
    exact (le_div_iff₀ hα).2 (by simpa [mul_comm] using h)
  have hlogn' : Real.log (n : ℝ) ≤ (m : ℝ) ^ (5 / 100 : ℝ) / α :=
    hlogn.trans (div_le_div_of_nonneg_right hlogm hα.le)
  have hJ : (Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) : ℝ) + 1 ≤
      2 * (m : ℝ) ^ (1 / 25 : ℝ) := by
    have hf := Nat.floor_le (Real.rpow_nonneg hmp.le (1 / 25 : ℝ))
    have h1 := Real.one_le_rpow hm1R (by norm_num : (0 : ℝ) ≤ 1 / 25)
    push_cast
    linarith
  have hsum : Real.log K + d₂ * (Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) + 1) *
      Real.log (n : ℝ) ≤ (m : ℝ) ^ (15 / 100 : ℝ) := by
    have hmul := mul_le_mul hJ hlogn' (Real.log_nonneg hn1) (by positivity)
    have hdp : 0 ≤ d₂ := by norm_num [d₂]
    have hterm : d₂ * (Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) + 1) *
        Real.log (n : ℝ) ≤ (2 * d₂ / α) * (m : ℝ) ^ (9 / 100 : ℝ) := by
      calc
        _ ≤ d₂ * ((2 * (m : ℝ) ^ (1 / 25 : ℝ)) *
            ((m : ℝ) ^ (5 / 100 : ℝ) / α)) := by
              simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmul hdp
        _ = (2 * d₂ / α) * (m : ℝ) ^ (9 / 100 : ℝ) := by
          rw [show (9 / 100 : ℝ) = 1 / 25 + 5 / 100 by norm_num,
            Real.rpow_add hmp]
          ring
    calc
      _ ≤ (1 + 2 * d₂ / α) * (m : ℝ) ^ (9 / 100 : ℝ) := by linarith
      _ ≤ (m : ℝ) ^ (6 / 100 : ℝ) * (m : ℝ) ^ (9 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_right hgrowth (by positivity)
      _ = (m : ℝ) ^ (15 / 100 : ℝ) := by rw [← Real.rpow_add hmp]; norm_num
  calc
    _ = Real.exp (Real.log K + d₂ * (Nat.floor ((m : ℝ) ^ (1 / 25 : ℝ)) + 1) *
        Real.log (n : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hK, Real.rpow_def_of_pos hnp]
      congr 2 <;> ring
    _ ≤ _ := Real.exp_le_exp.mpr hsum

/-- The true tag gate is a deletion test at the observed keys. -/
theorem histSupport_even_gate (X : Ctx6 γ p₀ K n N E G M) (hSupp : X.HistSupport)
    (H : X.Hist) (hH : X.histLaw.w H ≠ 0) (x : CubeVertex n) :
    X.tagGate H.1 (X.evenType x) (H.1.2.2 (X.evenType x).key) := by
  classical
  obtain ⟨_, _, _, hStep1, _, _⟩ := hSupp H hH
  have hkey : (X.evenType x).key = X.g.L.key x := by
    unfold Ctx6.evenType
    by_cases hj : X.g.L.severity x ≤ X.J <;> simp [makeType6, Type6.key, hj]
  intro ℓ hℓ y
  have hg := _root_.Lane_q_s06_loads.makeType6_obs_scope binAdjacent6
    (X.g.L.key x) (X.g.L.sign x) (X.g.L.flippable x) (X.g.L.severity x) X.J ℓ
    (by simpa [Ctx6.evenType] using hℓ)
  have hnear : ℓ.1 ∈ X.C (X.g.L.key x) := by
    rcases hg.1 with heq | hc
    · rw [heq]; simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
    · exact hc
  have hstep : ℓ.1 ∈ X.step1Keys := by
    apply Finset.mem_biUnion.mpr
    exact ⟨X.g.L.key x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, hnear⟩
  have hrev : (X.evenType x).key ∈ X.C ℓ.1 := by
    rw [hkey]
    have ha : keyAdjacent6 binAdjacent6 (X.g.L.key x) ℓ.1 := (Finset.mem_filter.mp hnear).2
    change X.g.L.key x ∈ keyNeighborhood6 binAdjacent6 ℓ.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with heq | heq | ⟨hb, hb', hi, hrest, hdist⟩
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl heq.symm)
    · exact Or.inr (Or.inr ⟨hb', hb, hi, fun j hj => (hrest j hj).symm,
        by simpa [Nat.dist_comm] using hdist⟩)
  simpa [Ctx6.hidPostRep, Ctx6.withTag] using (hStep1 ℓ.1 hstep).2 _ hrev y

end
end HypercubeRamsey.Lane_sol_s06_loadB
