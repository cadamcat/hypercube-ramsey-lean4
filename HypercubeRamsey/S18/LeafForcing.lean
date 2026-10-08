import HypercubeRamsey.S18.Nodes_sol_s18_3e
import HypercubeRamsey.S18.LeafForcing_q_s18_cylf

namespace HypercubeRamsey.S18.LeafForcing
open Classical
open scoped BigOperators
open HypercubeRamsey.Lane_sol_s18_3f

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

/-- owner: lane sol-s18-3e. Shared cylinder forcing on the actual pool/tape
experiment: prescribe all pools on `R` and a tape event local to `R`. -/
theorem cylinder_forcing (D : S18.LateData hPT) (R : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) (ht : target ∈ permPools D.geom)
    (event : Finset (Tapes D.fresh D.encoding.Ts))
    (hlocal : ∀ t u : Tapes D.fresh D.encoding.Ts,
      (∀ C ∈ R, t C = u C) → (t ∈ event ↔ u ∈ event))
    (A : Finset D.encoding.InitInput)
    (hA : ∀ x, x ∈ A ↔ (∀ C ∈ R, x.1 C = target C) ∧ x.2 ∈ event)
    (hpos : 0 < ∑ x ∈ A, D.encoding.permLaw.w x) :
    ∃ force : D.encoding.InitInput → FinLaw D.encoding.InitInput,
      FinLaw.map (FinLaw.bind D.encoding.permLaw force) Prod.snd =
        FinLaw.cond D.encoding.permLaw A hpos ∧
      ∀ x y, 0 < (force x).w y →
        (∀ C, C ∉ R → y.2 C = x.2 C) ∧
        ∀ (C : D.geom.Cell) (s : Fin (D.geom.nslot C)), C ∉ R →
          (∀ C' ∈ R, ∀ s' : Fin (D.geom.nslot C'),
            D.geom.cellPatch C' = D.geom.cellPatch C →
              (x.1 C s).1 ≠ (target C' s').1) →
          y.1 C s = x.1 C s := by
  exact Lane_q_s18_cylf.cylinder_forcing_proof D R target ht event hlocal A hA hpos

private theorem sigma_bin_eq {i j : Fin PT.tiling.m}
    (b : Bin PT.tiling i) (c : Bin PT.tiling j)
    (hij : i = j) (hbc : b.1 = c.1) :
    (⟨i, b⟩ : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) = ⟨j, c⟩ := by
  subst hij
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hbc))

/-- A positive coordinate fiber has a permutation-support representative. -/
theorem fiber_representative (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (a : TestView D region)
    (ha : 0 < ∑ x ∈ Finset.univ.filter (fun x => testView D region x = a),
      D.encoding.permLaw.w x) :
    ∃ z : D.encoding.InitInput, testView D region z = a ∧ z.1 ∈ permPools D.geom := by
  obtain ⟨z, hz, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt ha)
  have hw : 0 < D.encoding.permLaw.w z :=
    lt_of_le_of_ne (D.encoding.permLaw.nonneg z) (Ne.symm hne)
  exact ⟨z, (Finset.mem_filter.mp hz).2, permLaw_support D z hw⟩

/-- The tape part of a coordinate fiber. -/
noncomputable def fiberTapes (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (a : TestView D region) : Finset (Tapes D.fresh D.encoding.Ts) :=
  Finset.univ.filter fun t => ∀ C (h : C ∈ region), t C = a.2 ⟨C, h⟩

theorem fiberTapes_local (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (a : TestView D region) (t u : Tapes D.fresh D.encoding.Ts)
    (htu : ∀ C ∈ region, t C = u C) :
    t ∈ fiberTapes D region a ↔ u ∈ fiberTapes D region a := by
  simp only [fiberTapes, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h C hC
    rw [← htu C hC]
    exact h C hC
  · intro h C hC
    rw [htu C hC]
    exact h C hC

theorem fiber_iff (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (a : TestView D region) (z : D.encoding.InitInput) (hz : testView D region z = a)
    (x : D.encoding.InitInput) :
    x ∈ Finset.univ.filter (fun x => testView D region x = a) ↔
      (∀ C ∈ region, x.1 C = z.1 C) ∧ x.2 ∈ fiberTapes D region a := by
  subst hz
  rw [Finset.mem_filter, fiberTapes, Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun C hC => ?_, Finset.mem_univ _, fun C hC => ?_⟩
    · exact congrArg (fun v : TestView D region => v.1 ⟨C, hC⟩) h
    · exact congrArg (fun v : TestView D region => v.2 ⟨C, hC⟩) h
  · rintro ⟨hp, -, ht⟩
    refine ⟨Finset.mem_univ _, Prod.ext ?_ ?_⟩
    · funext C
      exact hp C.1 C.2
    · funext C
      exact ht C.1 C.2

/-- The image condition of `cylinder_forcing`, read off from the test's image tokens. -/
theorem image_condition_of_not_mem (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (a : TestView D region) (z : D.encoding.InitInput) (hz : testView D region z = a)
    (x : D.encoding.InitInput) (C : D.geom.Cell) (s : Fin (D.geom.nslot C))
    (hnot : (⟨D.geom.cellPatch C, x.1 C s⟩ :
      Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) ∉
        testImages D region (viewPools D region a)) :
    ∀ C' ∈ region, ∀ s' : Fin (D.geom.nslot C'),
      D.geom.cellPatch C' = D.geom.cellPatch C →
        (x.1 C s).1 ≠ (z.1 C' s').1 := by
  intro C' hC' s' hpatch heq
  apply hnot
  have hzC : z.1 C' = a.1 ⟨C', hC'⟩ := by
    subst hz
    rfl
  have hview : viewPools D region a C' = a.1 ⟨C', hC'⟩ := by
    simp [viewPools, hC']
  refine Finset.mem_image.mpr ⟨⟨C', s'⟩, ?_, ?_⟩
  · simp [testDomains, hC']
  · apply sigma_bin_eq
    · exact hpatch
    · change (viewPools D region a C' s').1 = (x.1 C s).1
      rw [hview, ← hzC]
      exact heq.symm

/-- With `LeafCoupling.images_cover`, every coordinate fiber of every region
has the forcing kernel required by `TestFiberForcing`. -/
theorem testFiberForcing_of_cover (D : S18.LateData hPT) (δ : ℝ)
    (L : S18.LeafCoupling D δ) (region : Finset D.geom.Cell) :
    Nonempty (TestFiberForcing D δ L region) := by
  have hcover : ImageCovered D δ L := L.images_cover
  have key : ∀ a : TestView D region,
      ∀ ha : 0 < ∑ x ∈ Finset.univ.filter (fun x => testView D region x = a),
        D.encoding.permLaw.w x,
      ∃ force : D.encoding.InitInput → FinLaw D.encoding.InitInput,
        FinLaw.map (FinLaw.bind D.encoding.permLaw force) Prod.snd =
          FinLaw.cond D.encoding.permLaw
            (Finset.univ.filter fun x => testView D region x = a) ha ∧
        ∀ x y, 0 < (force x).w y →
          ∀ i, ¬ testTouches D δ L region a i → x ∈ L.leaf i → y ∈ L.leaf i := by
    intro a ha
    obtain ⟨z, hz, hzperm⟩ := fiber_representative D region a ha
    obtain ⟨force, hpush, hloc⟩ := cylinder_forcing D region z.1 hzperm
      (fiberTapes D region a) (fiberTapes_local D region a)
      (Finset.univ.filter fun x => testView D region x = a)
      (fiber_iff D region a z hz) ha
    refine ⟨force, hpush, ?_⟩
    intro x y hxy i hi hx
    obtain ⟨htape, hpool⟩ := hloc x y hxy
    apply leaf_preserved_of_imageCovered D δ L hcover region a x y _ _ i hi hx
    · intro s hs himg
      have hsR : s.1 ∉ region := by
        intro h
        exact hs (by simp [testDomains, h])
      exact (hpool s.1 s.2 hsR
        (image_condition_of_not_mem D region a z hz x s.1 s.2 himg)).symm
    · intro C hC
      exact (htape C hC).symm
  exact ⟨{
    force := fun a ha => Classical.choose (key a ha)
    push := fun a ha => (Classical.choose_spec (key a ha)).1
    preserves := fun a ha => (Classical.choose_spec (key a ha)).2 }⟩

end HypercubeRamsey.S18.LeafForcing
