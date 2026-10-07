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

end HypercubeRamsey.S18.Lane_q_s18_n5
