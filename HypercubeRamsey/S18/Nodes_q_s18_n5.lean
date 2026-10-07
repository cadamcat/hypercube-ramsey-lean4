import HypercubeRamsey.S18.Defs

namespace HypercubeRamsey.S18.Lane_q_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

/-- The correlation cutoff used for pair support is symmetric in its two labels. -/
theorem nonconflict_symm (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) :
    D.nonconflict v x z ↔ D.nonconflict v z x := by
  unfold LateData.nonconflict
  have hcorr : pairCorr (T.S.E k) true (PT.π (D.geom.patchOf v)) x z =
      pairCorr (T.S.E k) true (PT.π (D.geom.patchOf v)) z x := by
    simp [pairCorr, corr, fv, mul_comm, mul_left_comm, mul_assoc]
  rw [hcorr]

/-- Endpoint symmetry of the explicitly defined isolate kernel. -/
theorem isolatedWeight_symm (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) :
    isolatedWeight D v x z = isolatedWeight D v z x := by
  simp [isolatedWeight, nonconflict_symm, mul_comm, mul_left_comm, mul_assoc,
    and_comm, and_left_comm, and_assoc]

theorem paletteRows_eq_counted (D : LateData hPT) (p : PaletteIndex D) :
    D.paletteRows p = Finset.univ.filter (fun v : Pos T k => IsEvenRole v ∧
      (D.geom.patchOf v = p.1 ∧ D.palette v = D.palettes p.1 p.2)) := by
  classical
  rcases p with ⟨i, a⟩
  apply Finset.ext
  intro v
  simp only [LateData.paletteRows, Finset.mem_filter, Finset.mem_univ]
  constructor
  · rintro ⟨_, he, hrole⟩
    rcases Sigma.mk.inj_iff.mp hrole with ⟨hpatch, hcolor⟩
    subst i
    have hcolor' : D.colourOf v = a := eq_of_heq hcolor
    exact ⟨trivial, he, rfl, by simp [LateData.palette, hcolor']⟩
  · rintro ⟨_, he, hpatch, hpalette⟩
    subst i
    have hcolor : D.colourOf v = a := by
      by_contra hne
      obtain ⟨x, hx⟩ := D.palette_nonempty (D.geom.patchOf v) (D.colourOf v)
      have hd := D.palette_disjoint (D.geom.patchOf v) (D.colourOf v) a hne
      have hx' : x ∈ D.palettes (D.geom.patchOf v) a := by
        simpa [LateData.palette] using hpalette ▸ hx
      exact (Finset.disjoint_left.mp hd hx) hx'
    exact ⟨trivial, he, Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq hcolor⟩⟩


/-- Nonnegativity of the isolate kernel follows from the inherited fresh-prior axiom. -/
theorem isolatedWeight_nonneg (D : LateData hPT) (v : Pos T k) (x z : Fin (T.S.N k)) :
    0 ≤ isolatedWeight D v x z := by
  classical
  unfold isolatedWeight
  split_ifs with hvalid
  · obtain ⟨validState, permittedLabels, hFresh⟩ := D.l16_valid.fresh_spec
    have hdeg (i : Fin PT.tiling.m) (y : Fin (T.S.N k)) :
        0 ≤ rowDeg (T.S.E k) PT.tiling.c y (PT.π i) := by
      unfold rowDeg
      apply Finset.sum_nonneg
      intro y' _
      by_cases h : Hits (T.S.E k) PT.tiling.c y y'
      · simp [h, (PT.π i).nonneg y']
      · simp [h]
    have hcore (pools : ∀ C, D.fresh.Pool C) (s : Config D.fresh) :
        0 ≤ D.sigma v s x * D.sigma v s z *
          ∏ a ∈ D.externalEarly v,
            (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)) ∧
              Hits (T.S.E k) PT.tiling.c z (D.earlyLabel s (flipPos v a)) then (1 : ℝ) else 0) /
              (rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) *
               rowDeg (T.S.E k) PT.tiling.c z (PT.π (D.geom.patchOf (flipPos v a)))) := by
      have hx : 0 ≤ D.sigma v s x := hFresh.prior_nonneg _ _ _ _
      have hz : 0 ≤ D.sigma v s z := hFresh.prior_nonneg _ _ _ _
      apply mul_nonneg (mul_nonneg hx hz)
      apply Finset.prod_nonneg
      intro a ha
      have hdx := hdeg (D.geom.patchOf (flipPos v a)) x
      have hdz := hdeg (D.geom.patchOf (flipPos v a)) z
      apply div_nonneg
      · split_ifs <;> norm_num
      · exact mul_nonneg hdx hdz
    have hinner (pools : ∀ C, D.fresh.Pool C) :
        0 ≤ (D.freshConfigLaw pools).E (fun s => D.sigma v s x * D.sigma v s z *
          ∏ a ∈ D.externalEarly v,
            (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)) ∧
              Hits (T.S.E k) PT.tiling.c z (D.earlyLabel s (flipPos v a)) then (1 : ℝ) else 0) /
              (rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) *
               rowDeg (T.S.E k) PT.tiling.c z (PT.π (D.geom.patchOf (flipPos v a))))) := by
      unfold FinLaw.E
      apply Finset.sum_nonneg
      intro s hs
      exact mul_nonneg ((D.freshConfigLaw pools).nonneg s) (hcore pools s)
    have hout : 0 ≤ D.encoding.iidLaw.E (fun pools =>
        if ∀ C ∈ D.directCells v, D.fresh.typical C (pools C) then
          (D.freshConfigLaw pools).E (fun s => D.sigma v s x * D.sigma v s z *
            ∏ a ∈ D.externalEarly v,
              (if Hits (T.S.E k) PT.tiling.c x (D.earlyLabel s (flipPos v a)) ∧
                Hits (T.S.E k) PT.tiling.c z (D.earlyLabel s (flipPos v a)) then (1 : ℝ) else 0) /
                (rowDeg (T.S.E k) PT.tiling.c x (PT.π (D.geom.patchOf (flipPos v a))) *
                 rowDeg (T.S.E k) PT.tiling.c z (PT.π (D.geom.patchOf (flipPos v a)))))
        else 0) := by
      unfold FinLaw.E
      apply Finset.sum_nonneg
      intro pools hpools
      by_cases ht : ∀ C ∈ D.directCells v, D.fresh.typical C (pools C)
      · simp only [if_pos ht]
        exact mul_nonneg (D.encoding.iidLaw.nonneg pools) (hinner pools)
      · simp only [if_neg ht]
        exact mul_nonneg (D.encoding.iidLaw.nonneg pools) (le_rfl)
    exact mul_nonneg (sq_nonneg (D.chi (D.geom.patchOf v) : ℝ)) hout
  · simp

private theorem graph_nonisolates_le_twice_rank {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : Finset V) (hN : ∀ v ∈ N, ∃ w, G.Adj v w) :
    N.card ≤ 2 * (Fintype.card V - Nat.card G.ConnectedComponent) := by
  classical
  let fiber (c : G.ConnectedComponent) : Finset V :=
    Finset.univ.filter fun v => G.connectedComponentMk v = c
  have hfiber_pos (c : G.ConnectedComponent) : 0 < (fiber c).card := by
    obtain ⟨v, hv⟩ := c.exists_rep
    apply Finset.card_pos.mpr
    refine ⟨v, ?_⟩
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    change G.connectedComponentMk v = c
    exact hv
  have hsum_fiber :
      Fintype.card V = ∑ c : G.ConnectedComponent, (fiber c).card := by
    simpa [fiber] using
      (Finset.card_eq_sum_card_fiberwise
        (f := fun v : V => G.connectedComponentMk v)
        (s := Finset.univ) (t := Finset.univ)
      (by intro v hv; simp))
  have hsub : N.card ≤
      ∑ c : G.ConnectedComponent,
        if 2 ≤ (fiber c).card then (fiber c).card else 0 := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun v : V => G.connectedComponentMk v) (s := N) (t := Finset.univ)
      (by intro v hv; simp)]
    apply Finset.sum_le_sum
    intro c hc
    by_cases hlarge : 2 ≤ (fiber c).card
    · have hsubset : (N.filter fun v => G.connectedComponentMk v = c) ⊆ fiber c := by
        intro v hv
        change v ∈ Finset.univ.filter (fun u => G.connectedComponentMk u = c)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      simpa [hlarge] using Finset.card_le_card hsubset
    · have hsmall : (fiber c).card < 2 := Nat.lt_of_not_ge hlarge
      have hnot : ∀ v ∈ N, G.connectedComponentMk v ≠ c := by
        intro v hvN heq
        obtain ⟨w, hadj⟩ := hN v hvN
        have hne : v ≠ w := G.ne_of_adj hadj
        have hwc : G.connectedComponentMk w = c := by
          rw [← heq]
          exact SimpleGraph.ConnectedComponent.sound hadj.symm.reachable
        have hmemV : v ∈ fiber c := by simp [fiber, heq]
        have hmemW : w ∈ fiber c := by simp [fiber, hwc]
        have hcard : 2 ≤ (fiber c).card := by
          exact Finset.one_lt_card.mpr ⟨v, hmemV, w, hmemW, hne⟩
        omega
      have hempty : (N.filter fun v => G.connectedComponentMk v = c) = ∅ :=
        Finset.filter_eq_empty_iff.mpr hnot
      simpa [hempty, hlarge]
  have hsum_sub :
      (∑ c : G.ConnectedComponent, ((fiber c).card - 1)) =
          Fintype.card V - Nat.card G.ConnectedComponent := by
    have hsum_decomp :
        (∑ c : G.ConnectedComponent, (fiber c).card) =
          (∑ c : G.ConnectedComponent, ((fiber c).card - 1)) +
            Fintype.card G.ConnectedComponent := by
      calc
        _ = ∑ c : G.ConnectedComponent, ((fiber c).card - 1 + 1) := by
          apply Finset.sum_congr rfl
          intro c hc
          have := hfiber_pos c
          omega
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp
    have hnat : Nat.card G.ConnectedComponent = Fintype.card G.ConnectedComponent :=
      Nat.card_eq_fintype_card
    omega
  calc
    N.card ≤ ∑ c : G.ConnectedComponent,
        if 2 ≤ (fiber c).card then (fiber c).card else 0 := hsub
    _ ≤ ∑ c : G.ConnectedComponent, 2 * ((fiber c).card - 1) := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hlarge : 2 ≤ (fiber c).card
      · have := hfiber_pos c
        simp [hlarge]
        omega
      · have hsmall : (fiber c).card < 2 := Nat.lt_of_not_ge hlarge
        have hone : (fiber c).card = 1 := by
          have := hfiber_pos c
          omega
        simp [hlarge, hone]
    _ = 2 * (Fintype.card V - Nat.card G.ConnectedComponent) := by
      rw [← Finset.mul_sum]
      rw [hsum_sub]

theorem nonisolates_le_twice_rank (D : LateData hPT) (S : Finset (Pos T k)) :
    (D.nonisolates S).card ≤ 2 * D.rank S := by
  classical
  let G := D.overlapGraph S
  let N : Finset {v : Pos T k // v ∈ S} :=
    S.attach.filter fun v => ∃ w ∈ S, D.geometricAdj v.1 w
  have hN : ∀ v ∈ N, ∃ w : {u : Pos T k // u ∈ S}, G.Adj v w := by
    intro v hv
    obtain ⟨w, hw, hadj⟩ := (Finset.mem_filter.mp hv).2
    exact ⟨⟨w, hw⟩, hadj⟩
  have hbound := graph_nonisolates_le_twice_rank G N hN
  have hcard : N.card = (D.nonisolates S).card := by
    simpa [N, LateData.nonisolates] using
      congrArg Finset.card
        (Finset.filter_attach (fun v : Pos T k => ∃ w ∈ S, D.geometricAdj v w) S)
  rw [hcard] at hbound
  simpa [G, LateData.rank, Nat.card_eq_fintype_card] using hbound

end HypercubeRamsey.S18.Lane_q_s18_n5
