import HypercubeRamsey.S18.Cost_sol_s18_n4
import HypercubeRamsey.S18.Test_sol_s18_n4
import HypercubeRamsey.S18.PoolBudget_sol_s18_n5
import HypercubeRamsey.S18.Swap_sol_s18_n4
import HypercubeRamsey.S18.Nodes_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_3f
open Classical Filter
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

private theorem graphBall_card (D : S18.LateData hPT) (d : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter fun w => D.encoding.events.Adjacent v w).card ≤ d)
    (seed : Finset (Pos T k)) (t : ℕ) :
    (D.encoding.events.graphBall seed t).card ≤ seed.card * (d + 1) ^ t := by
  induction t with
  | zero => simp [ListEvent.graphBall]
  | succ t ih =>
    let prev := D.encoding.events.graphBall seed t
    let nbr := fun v => Finset.univ.filter fun w => D.encoding.events.Adjacent v w
    have hsub : (Finset.univ.filter fun w =>
        ∃ v ∈ prev, D.encoding.events.Adjacent w v) ⊆ prev.biUnion nbr := by
      intro w hw
      obtain ⟨_, v, hv, hne, hdis⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_biUnion.mpr ⟨v, hv,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne.symm, fun h => hdis h.symm⟩⟩
    have hnext : (Finset.univ.filter fun w =>
        ∃ v ∈ prev, D.encoding.events.Adjacent w v).card ≤ prev.card * d := by
      exact (Finset.card_le_card hsub).trans
        (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hdegree v))
    change (prev ∪ Finset.univ.filter (fun w =>
      ∃ v ∈ prev, D.encoding.events.Adjacent w v)).card ≤ _
    calc
      _ ≤ prev.card + (Finset.univ.filter fun w =>
          ∃ v ∈ prev, D.encoding.events.Adjacent w v).card := Finset.card_union_le _ _
      _ ≤ prev.card + prev.card * d := Nat.add_le_add_left hnext _
      _ = prev.card * (d + 1) := by ring
      _ ≤ (seed.card * (d + 1) ^ t) * (d + 1) := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [pow_succ]; ring

private theorem incident_card (D : S18.LateData hPT) (d : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter fun w => D.encoding.events.Adjacent v w).card ≤ d)
    (C : D.geom.Cell) : (D.encoding.events.incidentEvents C).card ≤ d + 1 := by
  by_cases h : (D.encoding.events.incidentEvents C).Nonempty
  · obtain ⟨v, hv⟩ := h
    have hsub : D.encoding.events.incidentEvents C ⊆
        insert v (Finset.univ.filter fun w => D.encoding.events.Adjacent v w) := by
      intro w hw
      by_cases heq : w = v
      · exact heq ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, fun h => heq h.symm, ?_⟩
        apply Finset.not_disjoint_iff.mpr
        exact ⟨C, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hw).2⟩
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hdegree v) 1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

private theorem scope_card (D : S18.LateData hPT) (hD : D.Spec) (v : Pos T k) :
    (D.encoding.events.scope v).card ≤ T.S.n k + 1 := by
  rw [hD.scope_eq]
  calc
    (D.directCells v).card ≤ 1 + (D.externalEarly v).card := by
      exact (Finset.card_union_le _ _).trans (by
        simpa only [Finset.card_singleton] using Nat.add_le_add_left
          (Finset.card_image_le (s := D.externalEarly v)
            (f := fun a => D.geom.cellOf (flipPos v a))) 1)
    _ ≤ T.S.n k + 1 := by
      have h := Finset.card_le_card (Finset.filter_subset
        (fun a : Fin (T.S.n k) => a ∉ PT.tiling.Icoord (D.geom.patchOf v) ∧
          D.geom.classOf (flipPos v a) = none) Finset.univ)
      simpa only [S18.LateData.externalEarly, Finset.card_univ, Fintype.card_fin, add_comm]
        using Nat.add_le_add_left h 1

/-- Expanding an arbitrary seed costs its size times a fixed graph-growth factor. -/
theorem expandCells_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (seed : Finset D.geom.Cell) :
    (D.expandCells seed).card ≤ seed.card *
      (1 + (T.S.n k ^ (κ.Ac + 4) + 1) ^ (2 * D.encoding.Ts + 4) * (T.S.n k + 1)) := by
  let d := T.S.n k ^ (κ.Ac + 4)
  have hd := Lane_sol_s18_n4.eventDegreeBound D hD hn
  have hinc : (seed.biUnion D.encoding.events.incidentEvents).card ≤ seed.card * (d + 1) :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun C _ => incident_card D d hd C)
  have hgraph := graphBall_card D d hd (seed.biUnion D.encoding.events.incidentEvents)
    (2 * D.encoding.Ts + 3)
  have hregions : ((D.encoding.events.graphBall
      (seed.biUnion D.encoding.events.incidentEvents) (2 * D.encoding.Ts + 3)).biUnion
      D.encoding.events.scope).card ≤
      seed.card * (d + 1) ^ (2 * D.encoding.Ts + 4) * (T.S.n k + 1) := by
    calc
      _ ≤ (D.encoding.events.graphBall (seed.biUnion D.encoding.events.incidentEvents)
          (2 * D.encoding.Ts + 3)).card * (T.S.n k + 1) :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => scope_card D hD v)
      _ ≤ ((seed.card * (d + 1)) * (d + 1) ^ (2 * D.encoding.Ts + 3)) * (T.S.n k + 1) :=
        Nat.mul_le_mul_right _ (hgraph.trans (Nat.mul_le_mul_right _ hinc))
      _ = _ := by rw [show 2 * D.encoding.Ts + 4 = (2 * D.encoding.Ts + 3) + 1 by omega,
        pow_succ]; ring
  exact (Finset.card_union_le _ _).trans
    ((Nat.add_le_add_left hregions _).trans_eq (by dsimp [d]; ring))

noncomputable def testDomains (D : S18.LateData hPT) (region : Finset D.geom.Cell) :
    Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)) :=
  Finset.univ.filter fun s => s.1 ∈ region

noncomputable def testImages (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (pools : ∀ C, D.fresh.Pool C) :
    Finset (Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :=
  (testDomains D region).image fun s => ⟨D.geom.cellPatch s.1, pools s.1 s.2⟩

theorem testDomains_card (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (m : ℕ) (hm : ∀ C ∈ region, D.geom.nslot C ≤ m) :
    (testDomains D region).card ≤ region.card * m := by
  let J := region.biUnion fun C => (Finset.univ : Finset (Fin (D.geom.nslot C))).image
    (fun s => (⟨C, s⟩ : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)))
  have hsub : testDomains D region ⊆ J := by
    intro s hs
    exact Finset.mem_biUnion.mpr ⟨s.1, (Finset.mem_filter.mp hs).2,
      Finset.mem_image.mpr ⟨s.2, Finset.mem_univ _, rfl⟩⟩
  calc
    _ ≤ J.card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ region, ((Finset.univ : Finset (Fin (D.geom.nslot C))).image
        (fun s => (⟨C, s⟩ : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ C ∈ region, D.geom.nslot C := by
      exact Finset.sum_le_sum (fun C _ => (Finset.card_image_le).trans (by simp))
    _ ≤ ∑ _C ∈ region, m := Finset.sum_le_sum (fun C hC => hm C hC)
    _ = _ := by simp

private theorem seed_card_le_pow (D : S18.LateData hPT) (seed : Finset D.geom.Cell)
    (hn : 2 ≤ T.S.n k) (hseed : (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3)) :
    seed.card ≤ T.S.n k ^ D.encoding.Ts := by
  have hnpos : 0 < (T.S.n k : ℝ) := by exact_mod_cast (by omega : 0 < T.S.n k)
  have hlog : 0 ≤ Real.log (T.S.n k) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ T.S.n k))
  have hTs : Real.log (T.S.n k) ^ 2 ≤ (D.encoding.Ts : ℝ) := by
    rw [D.encoding.Ts_eq]
    exact Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_right hTs hlog
  have hbound : (seed.card : ℝ) ≤ (T.S.n k : ℝ) ^ D.encoding.Ts := by
    calc
      _ ≤ Real.exp (Real.log (T.S.n k) ^ 3) := hseed
      _ ≤ Real.exp ((D.encoding.Ts : ℝ) * Real.log (T.S.n k)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hnpos]
  exact_mod_cast hbound

private theorem growth_factor_le {n a t : ℕ} (hn : 2 ≤ n) :
    1 + (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1) ≤
      n ^ ((a + 5) * (2 * t + 4) + 3) := by
  have hp : 0 < n ^ (a + 4) := pow_pos (by omega) _
  have hd : n ^ (a + 4) + 1 ≤ n ^ (a + 5) := by
    calc
      _ ≤ n ^ (a + 4) * n := by nlinarith
      _ = _ := (pow_succ n (a + 4)).symm
  have hnp : n + 1 ≤ n ^ 2 := by nlinarith
  let z := (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1)
  have hz : 1 ≤ z := by
    have hh : 0 < (n ^ (a + 4) + 1) ^ (2 * t + 4) := pow_pos (by omega) _
    dsimp [z]
    nlinarith
  calc
    1 + z ≤ n * z := by nlinarith
    _ ≤ n * ((n ^ (a + 5)) ^ (2 * t + 4) * n ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hnp)
    _ = _ := by rw [← pow_mul]; ring

theorem testTokens_le (hκ : κ.Admissible) (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (hTs : 1 ≤ D.encoding.Ts) (hK : κ.Kcell ≤ (T.S.n k : ℝ))
    (seed : Finset D.geom.Cell) (hseed : (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3))
    (pools : ∀ C, D.fresh.Pool C) :
    (((testDomains D (D.expandCells seed)).card +
      (testImages D (D.expandCells seed) pools).card + (D.expandCells seed).card : ℕ) : ℝ) ≤
      Real.rpow (T.S.n k : ℝ) (10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ)) := by
  let n := T.S.n k
  let region := D.expandCells seed
  let m := n ^ (κ.Ac + 1)
  have hslots : ∀ C ∈ region, D.geom.nslot C ≤ m := by
    intro C _
    apply (S18.Lane_sol_s18_n5.slot_count_le_uniform hκ D C).trans
    apply Nat.ceil_le.mpr
    rw [Nat.cast_pow, pow_succ]
    simpa [n, mul_comm] using mul_le_mul_of_nonneg_right hK
      (pow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.Ac)
  have hreg : region.card ≤ n ^ (D.encoding.Ts + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) := by
    calc
      _ ≤ seed.card * (1 + (n ^ (κ.Ac + 4) + 1) ^ (2 * D.encoding.Ts + 4) * (n + 1)) :=
        expandCells_card D hD hn seed
      _ ≤ n ^ D.encoding.Ts * n ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) :=
        Nat.mul_le_mul (seed_card_le_pow D seed hn hseed) (growth_factor_le hn)
      _ = _ := by rw [← pow_add]; congr 1 <;> omega
  have hdom : (testDomains D region).card ≤ region.card * m := testDomains_card D region m hslots
  have himage : (testImages D region pools).card ≤ (testDomains D region).card := Finset.card_image_le
  have hm : 1 ≤ m := by
    have hp : 0 < n ^ (κ.Ac + 1) := pow_pos (by omega) _
    exact hp
  have hfactor : 2 * m + 1 ≤ n ^ (κ.Ac + 3) := by
    have hn2 : 4 ≤ n ^ 2 := by dsimp [n]; nlinarith
    have hmul := Nat.mul_le_mul_left m hn2
    rw [show κ.Ac + 3 = (κ.Ac + 1) + 2 by omega, pow_add]
    change 2 * m + 1 ≤ m * n ^ 2
    nlinarith
  have hexp : D.encoding.Ts + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3 + (κ.Ac + 3) ≤
      10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r) := by
    have hmul := Nat.mul_le_mul_left (8 * κ.Ac + 29) hTs
    nlinarith
  have hcount : (testDomains D region).card + (testImages D region pools).card + region.card ≤
      n ^ (10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r)) := by
    calc
      _ ≤ region.card * (2 * m + 1) := by nlinarith
      _ ≤ n ^ (D.encoding.Ts + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) * n ^ (κ.Ac + 3) :=
        Nat.mul_le_mul hreg hfactor
      _ = n ^ (D.encoding.Ts + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3 + (κ.Ac + 3)) :=
        (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by dsimp [n]; omega) hexp
  have he : 10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) =
      ((10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r) : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_eq_pow, Real.rpow_natCast]
  exact_mod_cast hcount

theorem testTokensEventually (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
      (D : S18.LateData hPT), D.Spec →
      ∀ seed : Finset D.geom.Cell, (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
      ∀ pools : ∀ C, D.fresh.Pool C,
        (((testDomains D (D.expandCells seed)).card +
          (testImages D (D.expandCells seed) pools).card + (D.expandCells seed).card : ℕ) : ℝ) ≤
          Real.rpow (T.S.n k : ℝ) (10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ)) := by
  have hnR := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp T.S.n_tendsto
  filter_upwards [Lane_sol_s18_n4.terminalScaleEventually κ T, hnR.eventually_ge_atTop κ.Kcell]
    with k hscale hK
  intro PT hPT D hD seed hseed pools
  obtain ⟨hn, hTs, hr⟩ := hscale D
  exact testTokens_le hκ D hD (by omega) (by exact_mod_cast hTs) hK seed hseed pools

abbrev TestView (D : S18.LateData hPT) (region : Finset D.geom.Cell) :=
  (∀ C : {C : D.geom.Cell // C ∈ region}, D.fresh.Pool C.1) ×
  (∀ C : {C : D.geom.Cell // C ∈ region}, Fin (D.encoding.Ts + 2) → TapeEntry D.fresh C.1)

noncomputable def testView (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (x : D.encoding.InitInput) : TestView D region :=
  (fun C => x.1 C.1, fun C => x.2 C.1)

noncomputable def viewPools (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (a : TestView D region) : ∀ C, D.fresh.Pool C :=
  fun C => if h : C ∈ region then a.1 ⟨C, h⟩ else D.encoding.pools_nonempty.choose C

theorem testView_local (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (x y : D.encoding.InitInput) (h : testView D region x = testView D region y) :
    ∀ C ∈ region, x.1 C = y.1 C ∧ x.2 C = y.2 C := by
  intro C hC
  exact ⟨congrArg (fun a : TestView D region => a.1 ⟨C, hC⟩) h,
    congrArg (fun a : TestView D region => a.2 ⟨C, hC⟩) h⟩

noncomputable def testTouches (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell)
    (a : TestView D region) (i : L.Leaf) : Prop :=
  ¬ Disjoint (L.domains i) (testDomains D region) ∨
    ¬ Disjoint (L.images i) (testImages D region (viewPools D region a)) ∨
    ¬ Disjoint (L.tapes i) region

/-- The remaining probabilistic obligation for a fixed deterministic test region. -/
structure TestFiberForcing (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell) where
  force : ∀ a : TestView D region,
    0 < ∑ x ∈ Finset.univ.filter (fun x => testView D region x = a), D.encoding.permLaw.w x →
      D.encoding.InitInput → FinLaw D.encoding.InitInput
  push : ∀ a ha,
    FinLaw.map (FinLaw.bind D.encoding.permLaw (force a ha)) Prod.snd =
      FinLaw.cond D.encoding.permLaw (Finset.univ.filter fun x => testView D region x = a) ha
  preserves : ∀ a ha x y, 0 < (force a ha x).w y →
    ∀ i, ¬ testTouches D δ L region a i → x ∈ L.leaf i → y ∈ L.leaf i

private theorem slice_eq_view (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (Ψ : D.encoding.InitInput → ℝ)
    (hlocal : ∀ x y, (∀ C ∈ region, x.1 C = y.1 C ∧ x.2 C = y.2 C) → Ψ x = Ψ y)
    (v : ℝ) (a : TestView D region)
    (hpos : 0 < ∑ x ∈ Finset.univ.filter (fun x => Ψ x = v ∧ testView D region x = a),
      D.encoding.permLaw.w x) :
    Finset.univ.filter (fun x => Ψ x = v ∧ testView D region x = a) =
      Finset.univ.filter (fun x => testView D region x = a) := by
  have hnonempty : (Finset.univ.filter (fun x => Ψ x = v ∧ testView D region x = a)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨x, hx⟩ := hnonempty
  obtain ⟨hxv, hxa⟩ := (Finset.mem_filter.mp hx).2
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro hya
    exact ⟨(hlocal y x (testView_local D region y x (hya.trans hxa.symm))).trans hxv, hya⟩

theorem testComparison_of_fiberForcing (D : S18.LateData hPT) (δ ε : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2)
    (hpositive : 0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x)
    (region : Finset D.geom.Cell) (forcing : TestFiberForcing D δ L region)
    (hcost : ∀ a : TestView D region,
      (∏ i ∈ Finset.univ.filter (testTouches D δ L region a),
        (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹) ≤ 1 + ε)
    (Ψ : D.encoding.InitInput → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x)
    (hlocal : ∀ x y, (∀ C ∈ region, x.1 C = y.1 C ∧ x.2 C = y.2 C) → Ψ x = Ψ y) :
    (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).E Ψ ≤
      (1 + ε) * D.encoding.permLaw.E Ψ := by
  refine Lane_sol_s18_n4.testComparisonFromForcingPartition D δ ε L hprob hcharge hpositive
    (testView D region) Ψ hΨ (fun _ a => testTouches D δ L region a)
    (fun v a ha => forcing.force a (by
      have ha' : 0 < ∑ x ∈ Finset.univ.filter (fun x => Ψ x = v ∧ testView D region x = a),
          D.encoding.permLaw.w x := by
        convert ha using 1 <;> congr 1 <;> ext x <;> simp
      rw [← slice_eq_view D region Ψ hlocal v a ha']
      exact ha')) ?_ ?_ ?_
  · intro v a ha
    rw [forcing.push]
    congr 1
    have ha' : 0 < ∑ x ∈ Finset.univ.filter (fun x => Ψ x = v ∧ testView D region x = a),
        D.encoding.permLaw.w x := by
      convert ha using 1 <;> congr 1 <;> ext x <;> simp
    convert (slice_eq_view D region Ψ hlocal v a ha').symm using 1 <;> ext x <;> simp
  · intro v a ha x y hxy i hi hleaf
    exact forcing.preserves a _ x y hxy i hi hleaf
  · exact fun _ a => hcost a

/-- An image-cover contract suffices to preserve a leaf under local image swaps. -/
def ImageCovered (D : S18.LateData hPT) (δ : ℝ) (L : S18.LeafCoupling D δ) : Prop :=
  ∀ i x, x ∈ L.leaf i → ∀ s ∈ L.domains i,
    (⟨D.geom.cellPatch s.1, x.1 s.1 s.2⟩ : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) ∈ L.images i

theorem leaf_preserved_of_imageCovered (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (himages : ImageCovered D δ L)
    (region : Finset D.geom.Cell) (a : TestView D region)
    (x y : D.encoding.InitInput)
    (hpool : ∀ s, s ∉ testDomains D region →
      (⟨D.geom.cellPatch s.1, x.1 s.1 s.2⟩ : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) ∉
        testImages D region (viewPools D region a) → x.1 s.1 s.2 = y.1 s.1 s.2)
    (htape : ∀ C, C ∉ region → x.2 C = y.2 C)
    (i : L.Leaf) (hi : ¬ testTouches D δ L region a i) (hx : x ∈ L.leaf i) : y ∈ L.leaf i := by
  have hdis : Disjoint (L.domains i) (testDomains D region) ∧
      Disjoint (L.images i) (testImages D region (viewPools D region a)) ∧
      Disjoint (L.tapes i) region := by
    simpa only [testTouches, not_or, not_not] using hi
  apply (L.depends_on i x y ?_ ?_).mp hx
  · intro s hs
    apply hpool s
    · exact fun h => Finset.disjoint_left.mp hdis.1 hs h
    · exact fun h => Finset.disjoint_left.mp hdis.2.1 (himages i x hx s hs) h
  · intro C hC
    exact htape C (fun h => Finset.disjoint_left.mp hdis.2.2 hC h)

/-- Omitting a leaf's occurring image makes disjoint-domain swap preservation false.
This finite example concerns that proof step, not the frozen terminal theorem. -/
theorem omittedImage_swap_example :
    Disjoint ({(1 : Fin 2)} : Finset (Fin 2)) {0} ∧
    Disjoint (∅ : Finset (Fin 2)) {1} ∧
    (Function.Embedding.refl (Fin 2)) 1 = 1 ∧
    Lane_sol_s18_n4.forceInjectionPin (0 : Fin 2) 1
      (Function.Embedding.refl (Fin 2)) 1 = 0 := by
  refine ⟨by decide, by simp, rfl, ?_⟩
  simp [Lane_sol_s18_n4.forceInjectionPin]

/-- For the two uniform permutations, the opposite slot pins are not lopsided
nonneighbors. Their domain slots are disjoint, but their prescribed image agrees. -/
theorem oppositePins_not_nonneighbors :
    let P := FinLaw.uniform (Finset.univ : Finset Bool) ⟨true, Finset.mem_univ _⟩
    P.pr (fun b => b = false ∧ b ≠ true) >
      P.pr (fun b => b = false) * P.pr (fun b => b ≠ true) := by
  norm_num [FinLaw.pr, FinLaw.uniform, Fintype.sum_bool]

/-- Image tokens may be erased when their edges were already carried by domains
or tapes. All fields of the frozen coupling contract remain satisfied. -/
noncomputable def eraseRedundantImages (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ)
    (hredundant : ∀ i j, ¬ Disjoint (L.images i) (L.images j) →
      ¬ Disjoint (L.domains i) (L.domains j) ∨ ¬ Disjoint (L.tapes i) (L.tapes j)) :
    S18.LeafCoupling D δ :=
  { L with
    images := fun _ => ∅
    adjacent_eq := by
      intro i j
      rw [L.adjacent_eq]
      simp only [Finset.disjoint_empty_left, not_true_eq_false, false_or]
      constructor
      · intro h
        rcases h with hd | him | ht
        · exact Or.inl hd
        · exact hredundant i j him
        · exact Or.inr ht
      · intro h
        rcases h with hd | ht
        · exact Or.inl hd
        · exact Or.inr (Or.inr ht)
    scope_bound := by
      intro i
      have h := L.scope_bound i
      have hi : 0 ≤ ((L.images i).card : ℝ) := Nat.cast_nonneg _
      simp only [Finset.card_empty, Nat.cast_zero, add_zero]
      push_cast at h ⊢
      linarith }

/-- Erasing redundant tokens rules out automatic image coverage for any occurring
leaf that reads a domain slot. This is a contract-level obstruction, not a
refutation of the terminal comparison theorem. -/
theorem erasedImages_not_imageCovered (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ)
    (hredundant : ∀ i j, ¬ Disjoint (L.images i) (L.images j) →
      ¬ Disjoint (L.domains i) (L.domains j) ∨ ¬ Disjoint (L.tapes i) (L.tapes j))
    (i : L.Leaf) (x : D.encoding.InitInput) (hx : x ∈ L.leaf i)
    (hdom : (L.domains i).Nonempty) :
    ¬ ImageCovered D δ (eraseRedundantImages D δ L hredundant) := by
  intro h
  obtain ⟨s, hs⟩ := hdom
  have hm := h i x hx s hs
  simpa [eraseRedundantImages] using hm

/-- Exact event inequality needed for coordinate fibers. This requires less
than an explicit forcing kernel. -/
def TestNonneighborBound (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell) : Prop :=
  ∀ (a : TestView D region) (S : Finset L.Leaf),
    (∀ i ∈ S, ¬ testTouches D δ L region a i) →
    D.encoding.permLaw.pr (fun x => testView D region x = a ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
      D.encoding.permLaw.pr (fun x => testView D region x = a) *
        D.encoding.permLaw.pr (fun x => ∀ i ∈ S, x ∉ L.leaf i)

private theorem pr_filter_mass {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (F : Ω → Prop) [DecidablePred F] :
    P.pr F = ∑ x ∈ Finset.univ.filter F, P.w x := by
  unfold FinLaw.pr
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hf : F x <;> simp [hf]

private theorem pr_nonneg {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (F : Ω → Prop) : 0 ≤ P.pr F := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg (fun x _ => by split_ifs <;> simp [P.nonneg])

theorem testNonneighbor_of_fiberForcing (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell)
    (forcing : TestFiberForcing D δ L region) : TestNonneighborBound D δ L region := by
  intro a S hS
  let F := fun x : D.encoding.InitInput => testView D region x = a
  by_cases ha : 0 < D.encoding.permLaw.pr F
  · have hmass : 0 < ∑ x ∈ Finset.univ.filter F, D.encoding.permLaw.w x := by
      exact lt_of_lt_of_eq ha (pr_filter_mass D.encoding.permLaw F)
    have h := Lane_sol_s18_n4.forcingLopsided D.encoding.permLaw
      (Finset.univ.filter F) hmass (forcing.force a hmass) (forcing.push a hmass)
      (fun x => ∀ i ∈ S, x ∉ L.leaf i) (by
        intro x y hxy hy i hi hx
        exact hy i hi (forcing.preserves a hmass x y hxy i (hS i hi) hx))
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h
  · have hz : D.encoding.permLaw.pr F = 0 :=
      le_antisymm (le_of_not_gt ha) (pr_nonneg _ _)
    change D.encoding.permLaw.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤ _
    have hle : D.encoding.permLaw.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
        D.encoding.permLaw.pr F := by
      unfold FinLaw.pr
      apply Finset.sum_le_sum
      intro x hx
      by_cases hf : F x
      · simp only [hf, true_and, ite_true]
        split_ifs <;> simp [D.encoding.permLaw.nonneg]
      · simp [hf]
    change _ ≤ D.encoding.permLaw.pr F * _
    rw [hz, zero_mul]
    exact hle.trans hz.le

private theorem pr_partition {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (partition : Ω → I) (F : Ω → Prop) :
    (∑ a, P.pr (fun x => F x ∧ partition x = a)) = P.pr F := by
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hf : F x <;> simp [hf]

set_option maxHeartbeats 400000 in
/-- The comparison follows from the fiber inequality without constructing
a stronger pointwise forcing kernel. -/
theorem testComparison_of_nonneighbor (D : S18.LateData hPT) (δ ε : ℝ)
    (L : S18.LeafCoupling D δ)
    (hprob : ∀ i, D.encoding.permLaw.pr (fun x => x ∈ L.leaf i) ≤ 1 / 4)
    (hcharge : ∀ i, (∑ j, if L.adjacent i j then
        2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf j) else 0) ≤ 1 / 2)
    (hpositive : 0 < ∑ x ∈ S18.terminalSet D δ, D.encoding.permLaw.w x)
    (region : Finset D.geom.Cell) (hnon : TestNonneighborBound D δ L region)
    (hcost : ∀ a : TestView D region,
      (∏ i ∈ Finset.univ.filter (testTouches D δ L region a),
        (1 - 2 * D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))⁻¹) ≤ 1 + ε)
    (Ψ : D.encoding.InitInput → ℝ) (hΨ : ∀ x, 0 ≤ Ψ x)
    (hlocal : ∀ x y, (∀ C ∈ region, x.1 C = y.1 C ∧ x.2 C = y.2 C) → Ψ x = Ψ y) :
    (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).E Ψ ≤
      (1 + ε) * D.encoding.permLaw.E Ψ := by
  apply Lane_sol_s18_n4.testComparisonFromFibers _ _ Ψ hΨ (1 + ε)
  intro v
  have hslice (a : TestView D region) :
      (D.encoding.terminalLaw (S18.terminalSet D δ) hpositive).pr
        (fun x => Ψ x = v ∧ testView D region x = a) ≤
      (1 + ε) * D.encoding.permLaw.pr
        (fun x => Ψ x = v ∧ testView D region x = a) := by
    let F := fun x : D.encoding.InitInput => Ψ x = v ∧ testView D region x = a
    have hF : ∀ S : Finset L.Leaf, (∀ i ∈ S, ¬ testTouches D δ L region a i) →
        D.encoding.permLaw.pr (fun x => F x ∧ ∀ i ∈ S, x ∉ L.leaf i) ≤
          D.encoding.permLaw.pr F * D.encoding.permLaw.pr (fun x => ∀ i ∈ S, x ∉ L.leaf i) := by
      intro S hS
      by_cases hex : ∃ x, F x
      · obtain ⟨x, hxv, hxa⟩ := hex
        have heq : F = fun y => testView D region y = a := by
          funext y
          apply propext
          constructor
          · exact And.right
          · intro hya
            exact ⟨(hlocal y x (testView_local D region y x (hya.trans hxa.symm))).trans hxv, hya⟩
        rw [heq]
        exact hnon a S hS
      · have hnone : ∀ x, ¬ F x := fun x hx => hex ⟨x, hx⟩
        simp only [FinLaw.pr, hnone, false_and, ite_false, Finset.sum_const_zero,
          zero_mul, le_refl]
    have hraw := Lane_sol_s18_n4.leafTestProbabilityBound D δ L hprob hcharge
      hpositive F (testTouches D δ L region a) hF
    have hmul := mul_le_mul_of_nonneg_left (hcost a) (pr_nonneg D.encoding.permLaw F)
    exact hraw.trans (hmul.trans_eq (mul_comm _ _))
  rw [← pr_partition _ (testView D region) (fun x => Ψ x = v),
    ← pr_partition D.encoding.permLaw (testView D region) (fun x => Ψ x = v),
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => hslice a)

private theorem pr_complement {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (F : Ω → Prop) :
    P.pr (fun x => ¬ F x) = 1 - P.pr F := by
  have hsum : P.pr (fun x => ¬ F x) + P.pr F = 1 := by
    rw [← P.sum_one]
    unfold FinLaw.pr
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hf : F x <;> simp [hf]
  linarith

/-- A positive coordinate fiber disjoint from a positive untouched leaf cannot
satisfy the required inequality. This diagnoses the forcing step only. -/
theorem testNonneighbor_fails_of_disjoint_leaf (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell)
    (a : TestView D region) (i : L.Leaf)
    (ha : 0 < D.encoding.permLaw.pr (fun x => testView D region x = a))
    (hi : 0 < D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))
    (huntouched : ¬ testTouches D δ L region a i)
    (hdis : ∀ x, 0 < D.encoding.permLaw.w x → testView D region x = a → x ∉ L.leaf i) :
    ¬ TestNonneighborBound D δ L region := by
  intro h
  have hb := h a {i} (by
    intro j hj
    have hji := Finset.mem_singleton.mp hj
    subst j
    exact huntouched)
  have heq : D.encoding.permLaw.pr
      (fun x => testView D region x = a ∧ ∀ j ∈ ({i} : Finset L.Leaf), x ∉ L.leaf j) =
      D.encoding.permLaw.pr (fun x => testView D region x = a) := by
    unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hw : 0 < D.encoding.permLaw.w x
    · by_cases hv : testView D region x = a
      · simp [hv, hdis x hw hv]
      · simp [hv]
    · have hz : D.encoding.permLaw.w x = 0 :=
        le_antisymm (le_of_not_gt hw) (D.encoding.permLaw.nonneg x)
      simp [hz]
  rw [heq] at hb
  have havoid : (fun x => ∀ j ∈ ({i} : Finset L.Leaf), x ∉ L.leaf j) =
      (fun x => x ∉ L.leaf i) := by funext x; simp
  rw [havoid, pr_complement] at hb
  have hp := mul_pos ha hi
  nlinarith

theorem no_testFiberForcing_of_disjoint_leaf (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell)
    (a : TestView D region) (i : L.Leaf)
    (ha : 0 < D.encoding.permLaw.pr (fun x => testView D region x = a))
    (hi : 0 < D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))
    (huntouched : ¬ testTouches D δ L region a i)
    (hdis : ∀ x, 0 < D.encoding.permLaw.w x → testView D region x = a → x ∉ L.leaf i) :
    ¬ Nonempty (TestFiberForcing D δ L region) := by
  rintro ⟨forcing⟩
  exact testNonneighbor_fails_of_disjoint_leaf D δ L region a i ha hi huntouched hdis
    (testNonneighbor_of_fiberForcing D δ L region forcing)

theorem permLaw_support (D : S18.LateData hPT) (x : D.encoding.InitInput)
    (hx : 0 < D.encoding.permLaw.w x) : x.1 ∈ permPools D.geom := by
  by_contra h
  have hz : D.encoding.permLaw.w x = 0 := by
    simp [LateEncoding.permLaw, LateEncoding.initialLaw, LateEncoding.poolLaw,
      permPoolLaw, FinLaw.bind, FinLaw.uniform, h]
  rw [hz] at hx
  exact lt_irrefl 0 hx

/-- In the actual permutation experiment, an outside prescribed pin and a
consulted test pin with the same image have disjoint positive supports.
If the supplied image tokens omit the collision, the test inequality fails. -/
theorem testNonneighbor_fails_of_omitted_pin (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell)
    (a : TestView D region) (i : L.Leaf)
    (ha : 0 < D.encoding.permLaw.pr (fun x => testView D region x = a))
    (hi : 0 < D.encoding.permLaw.pr (fun x => x ∈ L.leaf i))
    (huntouched : ¬ testTouches D δ L region a i)
    (s : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C))
    (hs : s ∈ L.domains i) (b : Bin PT.tiling (D.geom.cellPatch s.1))
    (hpin : ∀ x ∈ L.leaf i, x.1 s.1 s.2 = b)
    (C : D.geom.Cell) (hC : C ∈ region) (t : Fin (D.geom.nslot C))
    (hpatch : D.geom.cellPatch s.1 = D.geom.cellPatch C)
    (himage : b.1 = (a.1 ⟨C, hC⟩ t).1) :
    ¬ TestNonneighborBound D δ L region := by
  apply testNonneighbor_fails_of_disjoint_leaf D δ L region a i ha hi huntouched
  intro x hx hxa hleaf
  have hperm := (Finset.mem_filter.mp (permLaw_support D x hx)).2
  have htest : x.1 C t = a.1 ⟨C, hC⟩ t :=
    congrArg (fun z : TestView D region => z.1 ⟨C, hC⟩ t) hxa
  have heq : (x.1 s.1 s.2).1 = (x.1 C t).1 := by
    rw [hpin x hleaf, htest]
    exact himage
  have hcell := (hperm s.1 C s.2 t hpatch heq).1
  have htestdom : s ∈ testDomains D region := by
    simp only [testDomains, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcell.symm ▸ hC
  apply huntouched
  apply Or.inl
  intro hdis
  exact Finset.disjoint_left.mp hdis hs htestdom

/-- Every part of the terminal certificate follows once the exact missing
fiber inequality is supplied on the stated seed scopes. -/
theorem terminalCertificateEventually_of_nonneighbor
    {κ : CConsts} (hκ : κ.Admissible) (T : Stage) (δ : ℝ) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ D : S18.LateData hPT, D.Spec → S18.TerminalRiskBound D δ →
      ∀ L : S18.LeafCoupling D δ,
        (∀ seed : Finset D.geom.Cell,
          (seed.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
          TestNonneighborBound D δ L (D.expandCells seed)) →
        Nonempty (S18.TerminalCertificate D δ (T.S.n k : ℝ)⁻¹) := by
  filter_upwards [Lane_sol_s18_n4.terminalPositiveEventually hκ T δ,
    Lane_sol_s18_n4.terminalTestCostEventually hκ T δ,
    testTokensEventually hκ T] with k hpositive hcost htokens
  intro PT hPT D hD hRisk L hnon
  have hpos := hpositive D hRisk L
  obtain ⟨hprob, hcharge, hproduct⟩ := hcost D hRisk L
  refine ⟨Lane_q_s18_n4.terminalCertificateOfBounds D δ (T.S.n k : ℝ)⁻¹ hpos ?_⟩
  intro seed hseed Ψ hΨ hlocal
  apply testComparison_of_nonneighbor D δ (T.S.n k : ℝ)⁻¹ L hprob hcharge
    hpos (D.expandCells seed) (hnon seed hseed) ?_ Ψ hΨ hlocal
  intro a
  have hfilter : Finset.univ.filter (testTouches D δ L (D.expandCells seed) a) =
      Finset.univ.filter (fun i =>
        ¬ Disjoint (L.domains i) (testDomains D (D.expandCells seed)) ∨
        ¬ Disjoint (L.images i) (testImages D (D.expandCells seed)
          (viewPools D (D.expandCells seed) a)) ∨
        ¬ Disjoint (L.tapes i) (D.expandCells seed)) := by
    ext i
    simp only [Finset.mem_filter, testTouches]
  rw [hfilter]
  exact hproduct (testDomains D (D.expandCells seed))
    (testImages D (D.expandCells seed) (viewPools D (D.expandCells seed) a))
    (D.expandCells seed) (htokens D hD seed hseed (viewPools D (D.expandCells seed) a))

/-- An independent gate can make every one-pin risk arbitrarily small. It
does not repair an omitted image collision in a test's nonneighbor relation. -/
noncomputable def rareGateLaw (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FinLaw (Bool × Bool) where
  w x := (if x.2 then p else 1 - p) / 2
  nonneg x := by
    split_ifs
    · positivity
    · exact div_nonneg (sub_nonneg.mpr hp1) (by norm_num)
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true,
      ite_false, ite_true]
    ring

theorem rareGate_pinned_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    let P := rareGateLaw p hp0 hp1
    ∀ b : Bool, P.pr (fun x => x.1 = b ∧ x.1 = true ∧ x.2 = true) /
      P.pr (fun x => x.1 = b) ≤ p := by
  intro P b
  have hd : p / 2 + (1 - p) / 2 = (1 / 2 : ℝ) := by ring
  have heq : p / 2 / (1 / 2 : ℝ) = p := by ring
  cases b <;> simp [P, FinLaw.pr, rareGateLaw, Fintype.sum_prod_type, Fintype.sum_bool] <;>
    first | linarith | rw [hd, heq]

theorem rareGate_not_nonneighbor (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    let P := rareGateLaw p hp0.le hp1
    P.pr (fun x => x.1 = false ∧ ¬ (x.1 = true ∧ x.2 = true)) >
      P.pr (fun x => x.1 = false) * P.pr (fun x => ¬ (x.1 = true ∧ x.2 = true)) := by
  dsimp
  simp [FinLaw.pr, rareGateLaw, Fintype.sum_prod_type, Fintype.sum_bool]
  linarith

end HypercubeRamsey.Lane_sol_s18_3f
