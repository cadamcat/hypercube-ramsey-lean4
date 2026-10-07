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

private theorem flipPos_involutive (v : Pos T k) (a : Fin (T.S.n k)) :
    flipPos (flipPos v a) a = v := by
  funext j
  by_cases hj : j = a
  · subst j
    simp [flipPos]
  · simp [flipPos, hj]

private def oneNeighborhood (b : Pos T k) : Finset (Pos T k) :=
  insert b ((Finset.univ : Finset (Fin (T.S.n k))).image (fun a => flipPos b a))

private theorem oneNeighborhood_card (b : Pos T k) :
    (oneNeighborhood b).card ≤ T.S.n k + 1 := by
  classical
  unfold oneNeighborhood
  calc
    _ ≤ ((Finset.univ : Finset (Fin (T.S.n k))).image (fun a => flipPos b a)).card + 1 :=
      Finset.card_insert_le b _
    _ ≤ (Finset.univ : Finset (Fin (T.S.n k))).card + 1 :=
      Nat.add_le_add_right Finset.card_image_le 1
    _ = T.S.n k + 1 := by simp

private def cellSources (D : LateData hPT) (C : D.geom.Cell) : Finset (Pos T k) :=
  Finset.univ.filter fun b => D.geom.cellOf b = C

private def cellReach (D : LateData hPT) (C : D.geom.Cell) : Finset (Pos T k) :=
  (cellSources D C).biUnion oneNeighborhood

private theorem mem_cellReach_of_mem_directCells (D : LateData hPT) {C : D.geom.Cell}
    {w : Pos T k} (hC : C ∈ D.directCells w) : w ∈ cellReach D C := by
  classical
  simp only [LateData.directCells, Finset.mem_union, Finset.mem_singleton, Finset.mem_image] at hC
  rcases hC with hC | ⟨a, ha, hcell⟩
  · apply Finset.mem_biUnion.mpr
    refine ⟨w, ?_, ?_⟩
    · simp [cellSources, hC]
    · simp [oneNeighborhood]
  · let b := flipPos w a
    have hcell' : D.geom.cellOf b = C := by simpa [b] using hcell
    have hflip : flipPos b a = w := by simpa [b] using flipPos_involutive w a
    apply Finset.mem_biUnion.mpr
    refine ⟨b, ?_, ?_⟩
    · simp [cellSources, hcell']
    · change w ∈ insert b ((Finset.univ : Finset (Fin (T.S.n k))).image (fun a => flipPos b a))
      rw [← hflip]
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨a, Finset.mem_univ _, rfl⟩

private theorem cellSources_card_le (hκ : κ.Admissible) (D : LateData hPT)
    (C : D.geom.Cell) : (cellSources D C).card ≤ T.S.n k ^ 200 := by
  simpa [cellSources, hκ.Ac_eq] using D.l16_valid.cell_size C

private theorem cellReach_card_le (hκ : κ.Admissible) (D : LateData hPT)
    (C : D.geom.Cell) : (cellReach D C).card ≤ T.S.n k ^ 200 * (T.S.n k + 1) := by
  classical
  calc
    (cellReach D C).card ≤ ∑ b ∈ cellSources D C, (oneNeighborhood b).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ b ∈ cellSources D C, (T.S.n k + 1) := by
      apply Finset.sum_le_sum
      intro b hb
      exact oneNeighborhood_card b
    _ = (cellSources D C).card * (T.S.n k + 1) := by simp
    _ ≤ (T.S.n k ^ 200) * (T.S.n k + 1) :=
      Nat.mul_le_mul_right _ (cellSources_card_le hκ D C)

private theorem directCells_card_le (D : LateData hPT) (v : Pos T k) :
    (D.directCells v).card ≤ T.S.n k + 1 := by
  classical
  have hext : (D.externalEarly v).card ≤ T.S.n k := by
    simpa using (Finset.card_le_univ (D.externalEarly v))
  calc
    (D.directCells v).card ≤ 1 + ((D.externalEarly v).image
        (fun a => D.geom.cellOf (flipPos v a))).card := by
      simpa [LateData.directCells] using
        (Finset.card_union_le ({D.geom.cellOf v})
          ((D.externalEarly v).image (fun a => D.geom.cellOf (flipPos v a))))
    _ ≤ 1 + (D.externalEarly v).card := Nat.add_le_add_left Finset.card_image_le 1
    _ ≤ T.S.n k + 1 := by omega

private noncomputable def directPartnerSet (D : LateData hPT) (v : Pos T k) : Finset (Pos T k) :=
  Finset.univ.filter fun w => ¬ Disjoint (D.directCells v) (D.directCells w)

private noncomputable def directCandidates (D : LateData hPT) (v : Pos T k) : Finset (Pos T k) :=
  (D.directCells v).biUnion (cellReach D)

private theorem directPartner_subset_candidates (D : LateData hPT) (v : Pos T k) :
    directPartnerSet D v ⊆ directCandidates D v := by
  classical
  intro w hw
  have hnd : ¬ Disjoint (D.directCells v) (D.directCells w) :=
    (Finset.mem_filter.mp hw).2
  have hcommon : ∃ C, C ∈ D.directCells v ∧ C ∈ D.directCells w := by
    by_contra hn
    apply hnd
    apply Finset.disjoint_left.mpr
    intro C hCv hCw
    exact hn ⟨C, hCv, hCw⟩
  obtain ⟨C, hCv, hCw⟩ := hcommon
  apply Finset.mem_biUnion.mpr
  exact ⟨C, hCv, mem_cellReach_of_mem_directCells D hCw⟩

private theorem directCandidates_card_le (hκ : κ.Admissible) (D : LateData hPT)
    (v : Pos T k) :
    (directCandidates D v).card ≤ (T.S.n k + 1) * (T.S.n k ^ 200 * (T.S.n k + 1)) := by
  classical
  calc
    (directCandidates D v).card ≤
        ∑ C ∈ D.directCells v, (cellReach D C).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ D.directCells v, (T.S.n k ^ 200 * (T.S.n k + 1)) := by
      apply Finset.sum_le_sum
      intro C hC
      exact cellReach_card_le hκ D C
    _ = (D.directCells v).card * (T.S.n k ^ 200 * (T.S.n k + 1)) := by simp
    _ ≤ (T.S.n k + 1) * (T.S.n k ^ 200 * (T.S.n k + 1)) :=
      Nat.mul_le_mul_right _ (directCells_card_le D v)

private theorem hammingBall_two_card_le (v : Pos T k) :
    (hammingBall v 2).card ≤ (T.S.n k + 1) ^ 2 := by
  classical
  let B := hammingBall v 2
  let support (u : Pos T k) :=
    (Finset.univ : Finset (Fin (T.S.n k))).filter fun i => v i ≠ u i
  let Q := (Finset.univ : Finset (Fin (T.S.n k))).powerset.filter fun s => s.card ≤ 2
  have hsupport (u : Pos T k) : (support u).card = hammingDist v u := by
    simp [support, hammingDist]
  have hinj : Set.InjOn support (B : Set (Pos T k)) := by
    intro x hx y hy hxy
    funext i
    have hi : (v i ≠ x i) ↔ (v i ≠ y i) := by
      have hm := congrArg (fun s : Finset (Fin (T.S.n k)) => i ∈ s) hxy
      simpa [support] using hm
    cases hvi : v i <;> cases hxi : x i <;> cases hyi : y i <;> simp_all
  have himage : B.card = (B.image support).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hsubset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    have hu' : u ∈ hammingBall v 2 := by simpa [B] using hu
    have hd : hammingDist v u ≤ 2 := (Finset.mem_filter.mp hu').2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    calc
      (support u).card = hammingDist v u := hsupport u
      _ ≤ 2 := hd
  have hQsub : Q ⊆
      ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 0) ∪
        ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 1) ∪
          ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 2) := by
    intro s hs
    have hscard := (Finset.mem_filter.mp hs).2
    have hssub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    by_cases h0 : s.card = 0
    · have hm : s ∈ (Finset.univ : Finset (Fin (T.S.n k))).powersetCard 0 :=
        Finset.mem_powersetCard.mpr ⟨hssub, h0⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
    · by_cases h1 : s.card = 1
      · have hm : s ∈ (Finset.univ : Finset (Fin (T.S.n k))).powersetCard 1 :=
          Finset.mem_powersetCard.mpr ⟨hssub, h1⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
      · have h2 : s.card = 2 := by omega
        have hm : s ∈ (Finset.univ : Finset (Fin (T.S.n k))).powersetCard 2 :=
          Finset.mem_powersetCard.mpr ⟨hssub, h2⟩
        exact Finset.mem_union_right _ hm
  have hQcard : Q.card ≤ (T.S.n k + 1) ^ 2 := by
    calc
      Q.card ≤ (((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 0) ∪
          ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 1) ∪
          ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 2)).card :=
        Finset.card_le_card hQsub
      _ ≤ ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 0).card +
          ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 1).card +
          ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 2).card := by
        calc
          _ ≤ (((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 0) ∪
              ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 1)).card +
              ((Finset.univ : Finset (Fin (T.S.n k))).powersetCard 2).card :=
            Finset.card_union_le _ _
          _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (T.S.n k + 1) ^ 2 := by
        simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          Nat.choose_zero_right, Nat.choose_one_right]
        nlinarith [Nat.choose_le_pow (T.S.n k) 2]
  change B.card ≤ (T.S.n k + 1) ^ 2
  calc
    B.card = (B.image support).card := himage
    _ ≤ Q.card := Finset.card_le_card hsubset
    _ ≤ (T.S.n k + 1) ^ 2 := hQcard

private noncomputable def commonOddNeighborSet (v : Pos T k) : Finset (Pos T k) :=
  Finset.univ.filter fun w => ∃ b,
    (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v b ∧
    (OAI.HypercubeRamsey.cube (T.S.n k)).Adj w b

private theorem commonOddNeighbor_subset_hammingBall (v : Pos T k) :
    commonOddNeighborSet v ⊆ hammingBall v 2 := by
  intro w hw
  obtain ⟨b, hvb, hwb⟩ := (Finset.mem_filter.mp hw).2
  have hvb' : hammingDist v b = 1 := hvb
  have hwb' : hammingDist w b = 1 := hwb
  have hbw' : hammingDist b w = 1 := by
    have hs : hammingDist b w = hammingDist w b := by
      unfold hammingDist
      congr 1
      ext i
      simp [ne_comm]
    rw [hs, hwb']
  have hdist := hammingDist_triangle v b w
  rw [hvb', hbw'] at hdist
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hammingBall] using hdist⟩

theorem geometricAdj_degree_bound (hκ : κ.Admissible) (D : LateData hPT)
    (hn : 2 ≤ T.S.n k) (v : Pos T k) :
    ((Finset.univ.filter fun w => D.geometricAdj v w).card : ℝ) ≤
      (T.S.n k : ℝ) ^ (κ.Ac + 5) := by
  classical
  let direct := directPartnerSet D v
  let common := commonOddNeighborSet v
  let all := Finset.univ.filter fun w => D.geometricAdj v w
  have hdirect_sub : direct ⊆ directCandidates D v := directPartner_subset_candidates D v
  have hcommon_sub : common ⊆ hammingBall v 2 := commonOddNeighbor_subset_hammingBall v
  have hall_sub : all ⊆ direct ∪ common := by
    intro w hw
    rcases (Finset.mem_filter.mp hw).2 with ⟨_, hgeom⟩
    rcases hgeom with hdisj | hneighbor
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdisj⟩)
    · rcases hneighbor with ⟨b, hbclass, hvb, hwb⟩
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b, hvb, hwb⟩⟩)
  have hnpow : T.S.n k + 1 ≤ (T.S.n k) ^ 2 := by
    have hnreal : (2 : ℝ) ≤ T.S.n k := by exact_mod_cast hn
    have hreal : (T.S.n k : ℝ) + 1 ≤ (T.S.n k : ℝ) ^ 2 := by nlinarith
    exact_mod_cast hreal
  have hdirect : direct.card ≤ (T.S.n k) ^ 204 := by
    have hnpow2 : (T.S.n k + 1) ^ 2 ≤ ((T.S.n k) ^ 2) ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hnpow hnpow
    have hsquare : ((T.S.n k) ^ 2) ^ 2 = (T.S.n k) ^ 4 := by
      calc
        _ = (T.S.n k) ^ (2 * 2) := (pow_mul (T.S.n k) 2 2).symm
        _ = (T.S.n k) ^ 4 := by norm_num
    calc
      direct.card ≤ (T.S.n k + 1) * (T.S.n k ^ 200 * (T.S.n k + 1)) :=
        (Finset.card_le_card hdirect_sub).trans (directCandidates_card_le hκ D v)
      _ = (T.S.n k ^ 200) * (T.S.n k + 1) ^ 2 := by ring
      _ ≤ (T.S.n k ^ 200) * ((T.S.n k) ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ hnpow2
      _ = T.S.n k ^ 204 := by
        rw [hsquare]
        calc
          _ = (T.S.n k) ^ (200 + 4) := (pow_add (T.S.n k) 200 4).symm
          _ = (T.S.n k) ^ 204 := by norm_num
  have hball : (hammingBall v 2).card ≤ (T.S.n k) ^ 204 := by
    have hsquare : ((T.S.n k) ^ 2) ^ 2 = (T.S.n k) ^ 4 := by
      calc
        _ = (T.S.n k) ^ (2 * 2) := (pow_mul (T.S.n k) 2 2).symm
        _ = (T.S.n k) ^ 4 := by norm_num
    have hnpow4 : (T.S.n k + 1) ^ 2 ≤ (T.S.n k) ^ 4 := by
      calc
        _ ≤ ((T.S.n k) ^ 2) ^ 2 := by simpa [pow_two] using Nat.mul_le_mul hnpow hnpow
        _ = (T.S.n k) ^ 4 := hsquare
    have hone : 1 ≤ (T.S.n k) ^ 200 := Nat.one_le_pow 200 (T.S.n k) (by omega)
    have hpow : (T.S.n k) ^ 4 ≤ (T.S.n k) ^ 204 := by
      calc
        _ ≤ (T.S.n k) ^ 4 * (T.S.n k) ^ 200 := by
          simpa using Nat.mul_le_mul_left ((T.S.n k) ^ 4) hone
        _ = (T.S.n k) ^ 204 := by
          calc
            _ = (T.S.n k) ^ (4 + 200) := (pow_add (T.S.n k) 4 200).symm
            _ = (T.S.n k) ^ 204 := by norm_num
    exact (hammingBall_two_card_le v).trans (hnpow4.trans hpow)
  have hcommon : common.card ≤ (T.S.n k) ^ 204 :=
    (Finset.card_le_card hcommon_sub).trans hball
  have hsum : all.card ≤ 2 * (T.S.n k) ^ 204 := by
    calc
      all.card ≤ (direct ∪ common).card := Finset.card_le_card hall_sub
      _ ≤ direct.card + common.card := Finset.card_union_le _ _
      _ ≤ (T.S.n k) ^ 204 + (T.S.n k) ^ 204 := Nat.add_le_add hdirect hcommon
      _ = 2 * (T.S.n k) ^ 204 := by ring
  have hlast : 2 * (T.S.n k) ^ 204 ≤ (T.S.n k) ^ 205 := by
    calc
      _ ≤ (T.S.n k) * (T.S.n k) ^ 204 := Nat.mul_le_mul_right _ hn
      _ = (T.S.n k) ^ 204 * (T.S.n k) := by ac_rfl
      _ = (T.S.n k) ^ 205 := by
        calc
          _ = (T.S.n k) ^ (204 + 1) := (pow_succ (T.S.n k) 204).symm
          _ = (T.S.n k) ^ 205 := by norm_num
  have hnat : all.card ≤ (T.S.n k) ^ 205 := hsum.trans hlast
  have hreal : (all.card : ℝ) ≤ (T.S.n k : ℝ) ^ 205 := by exact_mod_cast hnat
  simpa [hκ.Ac_eq, Real.rpow_natCast] using hreal

end HypercubeRamsey.S18.Lane_q_s18_n5
