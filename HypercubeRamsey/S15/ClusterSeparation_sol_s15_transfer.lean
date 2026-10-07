import HypercubeRamsey.S15.ClusterNodes_sol_s15_transfer
import HypercubeRamsey.S15.ClusterNodes_q_s15_c2

namespace HypercubeRamsey.Lane_sol_s15_transfer

open Classical S15 Filter OAI.HypercubeRamsey
open scoped BigOperators

private theorem dependent_heq {α : Sort*} {β : α → Sort*}
    (f : ∀ a, β a) {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

theorem hd_comm {n : ℕ} (v w : CubeVertex n) : _root_.hammingDist v w = _root_.hammingDist w v :=
  _root_.hammingDist_comm v w

theorem hamming_restrict_le {n m : ℕ} (f : Fin m ↪ Fin n) (v w : CubeVertex n) :
    _root_.hammingDist (v ∘ f) (w ∘ f) ≤ _root_.hammingDist v w := by
  classical
  let A := Finset.univ.filter fun j : Fin m => v (f j) ≠ w (f j)
  let B := Finset.univ.filter fun j : Fin n => v j ≠ w j
  have hsub : A.image f ⊆ B := by
    intro j hj
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective A f.injective] at hcard
  exact hcard

theorem outside_dist_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v w : Position T k) :
    _root_.hammingDist (outsideWord PT hPT i v) (outsideWord PT hPT i w) ≤ _root_.hammingDist v w := by
  let f : Fin (T.S.n k - (PT.tiling.P i).h) ↪ Fin (T.S.n k) :=
    ⟨fun j => ⟨j.val, by have := j.isLt; omega⟩, by
      intro a b h
      exact Fin.ext (congrArg (fun x : Fin (T.S.n k) => x.val) h)⟩
  exact hamming_restrict_le f v w

theorem internal_dist_le {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v w : Position T k) :
    _root_.hammingDist (internalWord PT hPT i v) (internalWord PT hPT i w) ≤ _root_.hammingDist v w := by
  let f : Fin (PT.tiling.P i).h ↪ Fin (T.S.n k) :=
    ⟨fun j => ⟨T.S.n k - (PT.tiling.P i).h + j.val, by
      have := j.isLt; have := clusterHeight_le PT hPT i; omega⟩, by
      intro a b h
      apply Fin.ext
      have := congrArg Fin.val h
      change T.S.n k - (PT.tiling.P i).h + a.val =
        T.S.n k - (PT.tiling.P i).h + b.val at this
      omega⟩
  exact hamming_restrict_le f v w

theorem same_outside_dist_le_height {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v w : Position T k)
    (houtside : outsideWord PT hPT i v = outsideWord PT hPT i w) :
    _root_.hammingDist v w ≤ (PT.tiling.P i).h := by
  let f : Fin (PT.tiling.P i).h ↪ Fin (T.S.n k) :=
    ⟨fun j => ⟨T.S.n k - (PT.tiling.P i).h + j.val, by
      have := j.isLt; have := clusterHeight_le PT hPT i; omega⟩, by
      intro a b h
      apply Fin.ext
      have := congrArg Fin.val h
      change T.S.n k - (PT.tiling.P i).h + a.val =
        T.S.n k - (PT.tiling.P i).h + b.val at this
      omega⟩
  have hsub : (Finset.univ.filter fun j => v j ≠ w j) ⊆ Finset.univ.image f := by
    intro j hj
    have hne := (Finset.mem_filter.mp hj).2
    have hjge : T.S.n k - (PT.tiling.P i).h ≤ j.val := by
      by_contra h
      have hjlt : j.val < T.S.n k - (PT.tiling.P i).h := by omega
      have hx := congrFun houtside ⟨j.val, hjlt⟩
      exact hne (by simpa [outsideWord] using hx)
    let l : Fin (PT.tiling.P i).h :=
      ⟨j.val - (T.S.n k - (PT.tiling.P i).h), by
        have := j.isLt; have := clusterHeight_le PT hPT i; omega⟩
    refine Finset.mem_image.mpr ⟨l, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change T.S.n k - (PT.tiling.P i).h +
      (j.val - (T.S.n k - (PT.tiling.P i).h)) = j.val
    omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ f.injective] at hcard
  simpa [_root_.hammingDist] using hcard

theorem same_slice_dist_le_height {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v w : Position T k)
    (hs : clusterSliceAt PT hPT v = clusterSliceAt PT hPT w) :
    _root_.hammingDist v w ≤ (PT.tiling.P (patchAt PT hPT v)).h := by
  have hp := congrArg Sigma.fst hs
  have ho : HEq (outsideWord PT hPT (patchAt PT hPT v) v)
      (outsideWord PT hPT (patchAt PT hPT w) w) := by
    exact dependent_heq (fun s : ClusterSlice PT => s.2.1) hs
  have hw : HEq (outsideWord PT hPT (patchAt PT hPT w) w)
      (outsideWord PT hPT (patchAt PT hPT v) w) := by
    exact dependent_heq (fun i => outsideWord PT hPT i w) hp.symm
  apply same_outside_dist_le_height PT hPT (patchAt PT hPT v) v w
  exact eq_of_heq (ho.trans hw)

theorem adjacent_dist {T : Stage} {k : ℕ} {a : EvenPosition T k} {b : OddPosition T k}
    (h : Adjacent a b) : _root_.hammingDist a.1 b.1 = 1 := h

theorem crossing_same_slice_near {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (a a' : EvenPosition T k) (b b' : OddPosition T k)
    (hb : Adjacent a b) (hb' : Adjacent a' b')
    (hs : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT b'.1)
    (hwidth : ((PT.tiling.P (patchAt PT hPT b.1)).h : ℝ) + 2 ≤
      (T.S.n k : ℝ) ^ (2 * κ.ι)) :
    clusterCrossingNear PT a a' := by
  have h1 := _root_.hammingDist_triangle a.1 b.1 a'.1
  have h2 := _root_.hammingDist_triangle b.1 b'.1 a'.1
  have hh := same_slice_dist_le_height PT hPT b.1 b'.1 hs
  have hb1 := adjacent_dist hb
  have hb2 : _root_.hammingDist b'.1 a'.1 = 1 := by
    rw [hd_comm]
    exact adjacent_dist hb'
  have hnat : _root_.hammingDist a.1 a'.1 ≤ (PT.tiling.P (patchAt PT hPT b.1)).h + 2 := by omega
  have hreal : (_root_.hammingDist a.1 a'.1 : ℝ) ≤
      ((PT.tiling.P (patchAt PT hPT b.1)).h : ℝ) + 2 := by exact_mod_cast hnat
  exact hreal.trans hwidth

theorem allowed_crossing_slices_ne_of_rows_ne {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (M : ClusterMask PT)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι))
    {p q : Fin (T.S.n k) × OddPosition T k}
    (hp : p ∈ clusterAllowedCrossings PT hPT M)
    (hq : q ∈ clusterAllowedCrossings PT hPT M) (hne : p.1 ≠ q.1) :
    clusterSliceAt PT hPT p.2.1 ≠ clusterSliceAt PT hPT q.2.1 := by
  intro hs
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  have hpg : p.1 ∉ M.geometric := by
    have h := (Finset.mem_sdiff.mp hp'.1).2
    exact fun hg => h (Finset.mem_union_left _ hg)
  have hqg : q.1 ∉ M.geometric := by
    have h := (Finset.mem_sdiff.mp hq'.1).2
    exact fun hg => h (Finset.mem_union_left _ hg)
  have hnear := crossing_same_slice_near PT hPT (M.positions p.1) (M.positions q.1)
    p.2 q.2 (Finset.mem_filter.mp hp'.2.2).2.1
    (Finset.mem_filter.mp hq'.2.2).2.1 hs (hwidth _)
  apply hp'.2.1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.1, hpg, hqg, hne, hnear⟩

theorem adjacent_eq_flip {T : Stage} {k : ℕ} {a : EvenPosition T k} {b : OddPosition T k}
    (h : Adjacent a b) : ∃ j, b.1 = flipPos a.1 j := by
  classical
  have hcard : (Finset.univ.filter fun j => a.1 j ≠ b.1 j).card = 1 := h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  funext l
  by_cases hlj : l = j
  · subst l
    have hjmem : j ∈ Finset.univ.filter (fun l => a.1 l ≠ b.1 l) := by rw [hj]; simp
    have hne : a.1 j ≠ b.1 j := (Finset.mem_filter.mp hjmem).2
    cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [flipPos]
  · have heq : a.1 l = b.1 l := by
      by_contra hne
      have hmem : l ∈ Finset.univ.filter (fun j => a.1 j ≠ b.1 j) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ l, hne⟩
      rw [hj, Finset.mem_singleton] at hmem
      exact hlj hmem
    simpa [flipPos, hlj] using heq.symm

theorem crossing_patch_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    {b b' : OddPosition T k}
    (hb : b ∈ clusterCrossingNeighbours PT hPT a)
    (hb' : b' ∈ clusterCrossingNeighbours PT hPT a)
    (hp : patchAt PT hPT b.1 = patchAt PT hPT b'.1) : b = b' := by
  have hbparts := (Finset.mem_filter.mp hb).2
  have hb'parts := (Finset.mem_filter.mp hb').2
  obtain ⟨c, hc⟩ := adjacent_eq_flip hbparts.1
  obtain ⟨d, hd⟩ := adjacent_eq_flip hb'parts.1
  let j := patchAt PT hPT b.1
  have hleaf : b.1 ∈ PT.tiling.leaf j :=
    (Classical.choose_spec (hPT.tiling_valid.prefix_complete b.1)).1
  have hleaf' : b'.1 ∈ PT.tiling.leaf j := by
    rw [show j = patchAt PT hPT b'.1 from hp]
    exact (Classical.choose_spec (hPT.tiling_valid.prefix_complete b'.1)).1
  have hnot : a.1 ∉ PT.tiling.leaf j := by
    intro ha
    have huniq := (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).2 j ha
    exact hbparts.2 huniq
  have hcsmall : c.val < (PT.tiling.P j).ℓ := by
    by_contra hge
    apply hnot
    intro l hl
    have hne : l ≠ c := by intro h; subst l; omega
    have h := hleaf l hl
    rw [hc] at h
    simpa [flipPos, hne] using h
  have hcd : c = d := by
    by_contra hne
    have hbc := hleaf c hcsmall
    have hb'c := hleaf' c hcsmall
    rw [hc] at hbc
    rw [hd] at hb'c
    have heq := hbc.trans hb'c.symm
    cases ha : a.1 c <;> simp [flipPos, hne, ha] at heq
  apply Subtype.ext
  rw [hc, hd, hcd]

theorem allowed_crossing_slices_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (M : ClusterMask PT)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι)) :
    Set.InjOn (fun q : Fin (T.S.n k) × OddPosition T k => clusterSliceAt PT hPT q.2.1)
      (clusterAllowedCrossings PT hPT M) := by
  intro p hp q hq hs
  have hrows : p.1 = q.1 := by
    by_contra hne
    exact allowed_crossing_slices_ne_of_rows_ne PT hPT M hwidth hp hq hne hs
  apply Prod.ext hrows
  apply crossing_patch_injective PT hPT (M.positions p.1)
    (Finset.mem_filter.mp hp).2.2.2
  · simpa only [hrows] using (Finset.mem_filter.mp hq).2.2.2
  · exact congrArg Sigma.fst hs

theorem eventual_crossing_width (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι) := by
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have hp := (tendsto_rpow_atTop hκ.ι_rng.1).comp hn
  filter_upwards [hp.eventually (eventually_ge_atTop (2 : ℝ))] with k hk
  intro PT hPT j
  dsimp only [Function.comp_def] at hk
  have hh : ((PT.tiling.P j).h : ℝ) < (T.S.n k : ℝ) ^ κ.ι :=
    lt_of_le_of_lt (by exact_mod_cast le_max_left (PT.tiling.P j).h (PT.tiling.P j).ℓ)
      (hPT.tiling_valid.allocation_bounds j).1
  have heq : (T.S.n k : ℝ) ^ (2 * κ.ι) = ((T.S.n k : ℝ) ^ κ.ι) ^ (2 : ℕ) := by
    rw [mul_comm (2 : ℝ) κ.ι, Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_two]
  rw [heq]
  nlinarith

theorem flip_dist_one {n : ℕ} (v : CubeVertex n) (j : Fin n) :
    _root_.hammingDist (flipPos v j) v = 1 := by
  have heq : (Finset.univ.filter fun l => flipPos v j l ≠ v l) = {j} := by
    ext l
    by_cases hlj : l = j
    · subst l
      cases hv : v j <;> simp [flipPos, hv]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      have hsame : flipPos v j l = v l := by
        change Function.update v j (!v j) l = v l
        exact Function.update_of_ne hlj _ _
      simp only [hsame, ne_self_iff_false, hlj]
  change (Finset.univ.filter fun l => flipPos v j l ≠ v l).card = 1
  rw [heq]
  simp

noncomputable def solverWordFixed {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (v : Position T k) : IWord PT.tiling i :=
  let z := internalWord PT hPT i v
  if HypercubeRamsey.IsEvenRole z ↔ HypercubeRamsey.IsEvenRole v then z
  else flipPos z ⟨0, clusterHeight_pos PT hPT hm i⟩

theorem solver_word_fixed_heq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (v : Position T k) (hp : patchAt PT hPT v = i) :
    HEq (solverWordAt PT hPT hm v) (solverWordFixed PT hPT hm i v) :=
  dependent_heq (fun j => solverWordFixed PT hPT hm j v) hp

theorem solver_word_raw_dist_le_one {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (v : Position T k) :
    _root_.hammingDist (solverWordFixed PT hPT hm i v) (internalWord PT hPT i v) ≤ 1 := by
  unfold solverWordFixed
  dsimp only
  split_ifs
  · simp [_root_.hammingDist, _root_.hammingDist]
  · exact (flip_dist_one _ _).le

theorem solver_word_odd_fixed {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (b : OddPosition T k) :
    ¬ HypercubeRamsey.IsEvenRole (solverWordFixed PT hPT hm i b.1) := by
  unfold solverWordFixed
  dsimp only
  split_ifs with h
  · exact fun hz => b.2 (h.mp hz)
  · have hz : HypercubeRamsey.IsEvenRole (internalWord PT hPT i b.1) := by
      by_contra hn
      apply h
      exact ⟨fun hx => (hn hx).elim, fun hx => (b.2 hx).elim⟩
    exact fun hx => (evenRole_flipPos _ _).mp hx hz

theorem group_fiber_dist_le_two {κ : CConsts} {T : Stage} {k : ℕ}
    {𝒯 : Tiling κ T k} {i : Fin 𝒯.m} (g : Group 𝒯 i) {z z' : IWord 𝒯 i}
    (hz : z ∈ groupFiber g) (hz' : z' ∈ groupFiber g) : _root_.hammingDist z z' ≤ 2 := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp hz'
  have h := _root_.hammingDist_triangle (flipPos g.1 j) g.1 (flipPos g.1 j')
  have h1 := flip_dist_one g.1 j
  have h2 : _root_.hammingDist g.1 (flipPos g.1 j') = 1 := by
    rw [hd_comm]
    exact flip_dist_one _ _
  omega

theorem same_group_internal_dist_le_four {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (b b' : OddPosition T k)
    (hp : patchAt PT hPT b.1 = i) (hp' : patchAt PT hPT b'.1 = i)
    (hg : clusterGroupIndexAt PT hPT hm b = clusterGroupIndexAt PT hPT hm b') :
    _root_.hammingDist (internalWord PT hPT i b.1) (internalWord PT hPT i b'.1) ≤ 4 := by
  let S := clusterSolver PT hPT hm i
  have hkey := congrArg (fun g : ClusterGroupIndex PT =>
    (⟨g.1.1, g.2⟩ : Σ j : Fin PT.tiling.m, Group PT.tiling j)) hg
  change (⟨patchAt PT hPT b.1,
    (clusterSolver PT hPT hm (patchAt PT hPT b.1)).groupOf
      (solverWordFixed PT hPT hm (patchAt PT hPT b.1) b.1)⟩ :
    Σ j : Fin PT.tiling.m, Group PT.tiling j) =
    ⟨patchAt PT hPT b'.1,
      (clusterSolver PT hPT hm (patchAt PT hPT b'.1)).groupOf
        (solverWordFixed PT hPT hm (patchAt PT hPT b'.1) b'.1)⟩ at hkey
  rw [hp, hp'] at hkey
  have hgroup : S.groupOf (solverWordFixed PT hPT hm i b.1) =
      S.groupOf (solverWordFixed PT hPT hm i b'.1) := eq_of_heq (Sigma.mk.inj_iff.mp hkey).2
  have hb := S.groupOf_spec _ (solver_word_odd_fixed PT hPT hm i b)
  have hb' := S.groupOf_spec _ (solver_word_odd_fixed PT hPT hm i b')
  rw [← hgroup] at hb'
  have hmiddle := group_fiber_dist_le_two _ hb hb'
  have hleft : _root_.hammingDist (internalWord PT hPT i b.1) (solverWordFixed PT hPT hm i b.1) ≤ 1 := by
    rw [hd_comm]
    exact solver_word_raw_dist_le_one PT hPT hm i b.1
  have hright := solver_word_raw_dist_le_one PT hPT hm i b'.1
  have h1 := _root_.hammingDist_triangle (internalWord PT hPT i b.1)
    (solverWordFixed PT hPT hm i b.1) (internalWord PT hPT i b'.1)
  have h2 := _root_.hammingDist_triangle (solverWordFixed PT hPT hm i b.1)
    (solverWordFixed PT hPT hm i b'.1) (internalWord PT hPT i b'.1)
  omega

theorem same_slice_outside_eq_on_patch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (v w : Position T k) (hp : patchAt PT hPT v = i) (hp' : patchAt PT hPT w = i)
    (hs : clusterSliceAt PT hPT v = clusterSliceAt PT hPT w) :
    outsideWord PT hPT i v = outsideWord PT hPT i w := by
  have ho := dependent_heq (fun s : ClusterSlice PT => s.2.1) hs
  change HEq (outsideWord PT hPT (patchAt PT hPT v) v)
    (outsideWord PT hPT (patchAt PT hPT w) w) at ho
  rw [hp, hp'] at ho
  exact eq_of_heq ho

theorem intersecting_core_groups_near {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a a' : EvenPosition T k)
    (ha : patchAt PT hPT a.1 = i) (ha' : patchAt PT hPT a'.1 = i)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h)
    {g : ClusterGroupIndex PT}
    (hg : g ∈ clusterCoreGroups PT hPT hm a)
    (hg' : g ∈ clusterCoreGroups PT hPT hm a') : clusterCoreNear PT hPT i a a' := by
  obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp hg
  obtain ⟨b', hb', hbg'⟩ := Finset.mem_image.mp hg'
  have hparts := (Finset.mem_filter.mp hb).2
  have hparts' := (Finset.mem_filter.mp hb').2
  have hp : patchAt PT hPT b.1 = i := hparts.2.trans ha
  have hp' : patchAt PT hPT b'.1 = i := hparts'.2.trans ha'
  have hgroups := hbg.trans hbg'.symm
  have hs := congrArg Sigma.fst hgroups
  have hout := same_slice_outside_eq_on_patch PT hPT i b.1 b'.1 hp hp' hs
  have hi := same_group_internal_dist_le_four PT hPT hm i b b' hp hp' hgroups
  have hab := adjacent_dist hparts.1
  have hab' : _root_.hammingDist b'.1 a'.1 = 1 := by
    rw [hd_comm]
    exact adjacent_dist hparts'.1
  have ho1 := outside_dist_le PT hPT i a.1 b.1
  have ho2 := outside_dist_le PT hPT i b'.1 a'.1
  have hot := _root_.hammingDist_triangle (outsideWord PT hPT i a.1)
    (outsideWord PT hPT i b.1) (outsideWord PT hPT i a'.1)
  rw [hout] at hot ho1
  have hou : _root_.hammingDist (outsideWord PT hPT i a.1) (outsideWord PT hPT i a'.1) ≤ 2 := by omega
  have hi1 := internal_dist_le PT hPT i a.1 b.1
  have hi2 := internal_dist_le PT hPT i b'.1 a'.1
  have hit := _root_.hammingDist_triangle (internalWord PT hPT i a.1)
    (internalWord PT hPT i b.1) (internalWord PT hPT i a'.1)
  have hit' := _root_.hammingDist_triangle (internalWord PT hPT i b.1)
    (internalWord PT hPT i b'.1) (internalWord PT hPT i a'.1)
  have hin : _root_.hammingDist (internalWord PT hPT i a.1) (internalWord PT hPT i a'.1) ≤ 6 := by omega
  constructor
  · have hreal : (_root_.hammingDist (outsideWord PT hPT i a.1)
        (outsideWord PT hPT i a'.1) : ℝ) ≤ 2 := by exact_mod_cast hou
    linarith
  · have hreal : (_root_.hammingDist (internalWord PT hPT i a.1)
        (internalWord PT hPT i a'.1) : ℝ) ≤ 6 := by exact_mod_cast hin
    exact hreal.trans hradius

theorem geometrically_retained_not_core_near {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    {r t : Fin (T.S.n k)} (hr : r ∉ M.geometric) (ht : t ∉ M.geometric) (hrt : r ≠ t) :
    ¬ clusterCoreNear PT hPT i (M.positions r) (M.positions t) := by
  intro hnear
  rcases lt_or_gt_of_ne hrt with hrt | htr
  · exact ht ((hM.2.1 t).mpr ⟨r, hrt, hnear⟩)
  · exact hr ((hM.2.1 r).mpr ⟨t, htr, (core_near_symm PT hPT i _ _).mp hnear⟩)

theorem geometrically_retained_core_groups_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h)
    {r t : Fin (T.S.n k)} (hr : r ∉ M.geometric) (ht : t ∉ M.geometric) (hrt : r ≠ t) :
    Disjoint (clusterCoreGroups PT hPT hm (M.positions r))
      (clusterCoreGroups PT hPT hm (M.positions t)) := by
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  apply geometrically_retained_not_core_near PT hPT i M hM hr ht hrt
  exact intersecting_core_groups_near PT hPT hm i (M.positions r) (M.positions t)
    (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r))
    (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 t)) hradius hg hg'

/-- A geometric enclosure of every primitive record read by an internal or bulk core experiment. -/
noncomputable def coreRecordFootprint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterRecordIndex PT hPT hm) :=
  Finset.univ.filter fun r => patchAt PT hPT a.1 = r.1.1 ∧
    (_root_.hammingDist (outsideWord PT hPT r.1.1 a.1) r.1.2.1 : ℝ) ≤ 1 ∧
    (_root_.hammingDist (internalWord PT hPT r.1.1 a.1)
      ((clusterSolver PT hPT hm r.1.1).loc r.2) : ℝ) ≤
        10 * κ.ρ * (PT.tiling.P r.1.1).h + 3

theorem intersecting_core_record_footprints_near {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (a a' : EvenPosition T k)
    (ha : patchAt PT hPT a.1 = i) (ha' : patchAt PT hPT a'.1 = i)
    (hradius : (1 : ℝ) ≤ κ.ρ * (PT.tiling.P i).h)
    {r : ClusterRecordIndex PT hPT hm}
    (hr : r ∈ coreRecordFootprint PT hPT hm a)
    (hr' : r ∈ coreRecordFootprint PT hPT hm a') : clusterCoreNear PT hPT i a a' := by
  have h := (Finset.mem_filter.mp hr).2
  have h' := (Finset.mem_filter.mp hr').2
  have hi : r.1.1 = i := h.1.symm.trans ha
  have ho := _root_.hammingDist_triangle (outsideWord PT hPT r.1.1 a.1)
    r.1.2.1 (outsideWord PT hPT r.1.1 a'.1)
  have hoR : (_root_.hammingDist (outsideWord PT hPT r.1.1 a.1)
      (outsideWord PT hPT r.1.1 a'.1) : ℝ) ≤ 2 := by
    have ho' : (_root_.hammingDist (outsideWord PT hPT r.1.1 a.1)
        (outsideWord PT hPT r.1.1 a'.1) : ℝ) ≤
        _root_.hammingDist (outsideWord PT hPT r.1.1 a.1) r.1.2.1 +
          _root_.hammingDist r.1.2.1 (outsideWord PT hPT r.1.1 a'.1) := by exact_mod_cast ho
    rw [hd_comm r.1.2.1] at ho'
    linarith [h.2.1, h'.2.1]
  have hin := _root_.hammingDist_triangle (internalWord PT hPT r.1.1 a.1)
    ((clusterSolver PT hPT hm r.1.1).loc r.2) (internalWord PT hPT r.1.1 a'.1)
  have hinR : (_root_.hammingDist (internalWord PT hPT r.1.1 a.1)
      (internalWord PT hPT r.1.1 a'.1) : ℝ) ≤
      20 * κ.ρ * (PT.tiling.P r.1.1).h + 6 := by
    have hin' : (_root_.hammingDist (internalWord PT hPT r.1.1 a.1)
        (internalWord PT hPT r.1.1 a'.1) : ℝ) ≤
        _root_.hammingDist (internalWord PT hPT r.1.1 a.1)
          ((clusterSolver PT hPT hm r.1.1).loc r.2) +
        _root_.hammingDist ((clusterSolver PT hPT hm r.1.1).loc r.2)
          (internalWord PT hPT r.1.1 a'.1) := by exact_mod_cast hin
    rw [hd_comm ((clusterSolver PT hPT hm r.1.1).loc r.2)] at hin'
    linarith [h.2.2, h'.2.2]
  rw [hi] at hoR hinR
  exact ⟨by linarith, by nlinarith⟩

theorem geometrically_retained_core_records_disjoint {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (1 : ℝ) ≤ κ.ρ * (PT.tiling.P i).h)
    {r t : Fin (T.S.n k)} (hr : r ∉ M.geometric) (ht : t ∉ M.geometric) (hrt : r ≠ t) :
    Disjoint (coreRecordFootprint PT hPT hm (M.positions r))
      (coreRecordFootprint PT hPT hm (M.positions t)) := by
  apply Finset.disjoint_left.mpr
  intro g hg hg'
  apply geometrically_retained_not_core_near PT hPT i M hM hr ht hrt
  exact intersecting_core_record_footprints_near PT hPT hm i (M.positions r) (M.positions t)
    (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r))
    (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 t)) hradius hg hg'

theorem eventual_core_radius (κ : CConsts) (hκ : κ.Admissible) (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, ∀ hPT : PT.Valid,
      ∀ hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge,
      ∀ i, (1 : ℝ) ≤ κ.ρ * (PT.tiling.P i).h := by
  have hMlo : 0 < κ.Mlo := by
    by_contra h
    have hz : κ.Mlo = 0 := by omega
    have hupper := hκ.cq_rng.2
    simp only [hz, Nat.cast_zero, mul_zero, div_zero] at hupper
    linarith [hκ.cq_rng.1]
  have hMloR : (1 : ℝ) ≤ κ.Mlo := by exact_mod_cast hMlo
  have hcq2 : κ.cq ≤ 2 := by
    have hden : (0 : ℝ) < 20 * κ.Mlo := by positivity
    have hupper := (lt_div_iff₀ hden).mp hκ.cq_rng.2
    nlinarith [hκ.cq_rng.1]
  have hMhi : (0 : ℝ) < κ.Mhi := by
    have hm : (0 : ℝ) ≤ κ.Mhi := Nat.cast_nonneg _
    nlinarith [hκ.Mhi_big.2, hκ.cq_rng.1]
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp T.S.n_tendsto
  have ht := Real.tendsto_log_atTop.comp hn
  have hq := (tendsto_rpow_atTop hκ.cq_rng.1).comp ht
  have hh := (tendsto_rpow_atTop hMhi).comp hq
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ)),
    hh.eventually (eventually_ge_atTop (1 / κ.ρ))] with k ht1 hh1
  intro PT hPT hm i
  rcases hPT.tiling_valid.cluster_data (Or.inr hm) i with
    ⟨_, _, _, _, _, _, _, hheight, _, _, hsmall, hlarge⟩
  have hqbound : (Real.log (T.S.n k : ℝ)) ^ κ.cq ≤ (PT.tiling.P i).q := by
    rcases hm with hs | hl
    · exact (hsmall.mp hs).1.le
    · have hlt := hlarge.mp hl
      have ht1' : 1 ≤ Real.log (T.S.n k : ℝ) := ht1
      have hbase := Real.rpow_le_rpow_of_exponent_le ht1' hcq2
      rw [Real.rpow_two] at hbase
      exact hbase.trans hlt.le
  have hheight' : Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mhi : ℝ) ≤ (PT.tiling.P i).h := by
    have hnot : PT.tiling.mode ≠ .lowCluster := by
      rcases hm with hs | hl
      · simp [hs]
      · simp [hl]
    simpa only [if_neg hnot] using hheight
  have hlargeHeight : (1 / κ.ρ : ℝ) ≤ (PT.tiling.P i).h := by
    calc
      _ ≤ ((Real.log (T.S.n k : ℝ)) ^ κ.cq) ^ (κ.Mhi : ℝ) := hh1
      _ ≤ Real.rpow ((PT.tiling.P i).q : ℝ) (κ.Mhi : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg (zero_le_one.trans ht1) _) hqbound hMhi.le
      _ ≤ _ := hheight'
  have hρ := hκ.ρ_rng.1
  have hm := mul_le_mul_of_nonneg_left hlargeHeight hρ.le
  rw [mul_one_div_cancel hρ.ne'] at hm
  exact hm

theorem row_consultation_scope_subset_core {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    clusterConsultationScope PT hPT hm {rowConsultation PT hPT hm a} ⊆
      coreRecordFootprint PT hPT hm a := by
  rintro ⟨s, r⟩ hr
  obtain ⟨c, hc, e, hnear⟩ := (Finset.mem_filter.mp hr).2
  have hc' : c = rowConsultation PT hPT hm a := Finset.mem_singleton.mp hc
  subst c
  change clusterSliceAt PT hPT a.1 = s at e
  subst s
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, rfl, ?_, ?_⟩
  · change (_root_.hammingDist (outsideWord PT hPT (patchAt PT hPT a.1) a.1)
      (outsideWord PT hPT (patchAt PT hPT a.1) a.1) : ℝ) ≤ 1
    simp
  · let i := patchAt PT hPT a.1
    change (_root_.hammingDist (internalWord PT hPT i a.1)
      ((clusterSolver PT hPT hm i).loc r) : ℝ) ≤ 10 * κ.ρ * (PT.tiling.P i).h + 3
    have hshift := solver_word_raw_dist_le_one PT hPT hm i a.1
    have htri := _root_.hammingDist_triangle (internalWord PT hPT i a.1)
      (solverWordFixed PT hPT hm i a.1) ((clusterSolver PT hPT hm i).loc r)
    have htriR : (_root_.hammingDist (internalWord PT hPT i a.1)
        ((clusterSolver PT hPT hm i).loc r) : ℝ) ≤
        _root_.hammingDist (internalWord PT hPT i a.1) (solverWordFixed PT hPT hm i a.1) +
          _root_.hammingDist (solverWordFixed PT hPT hm i a.1) ((clusterSolver PT hPT hm i).loc r) :=
      by exact_mod_cast htri
    rw [hd_comm (internalWord PT hPT i a.1) (solverWordFixed PT hPT hm i a.1),
      hd_comm (solverWordFixed PT hPT hm i a.1) ((clusterSolver PT hPT hm i).loc r)] at htriR
    have hshiftR : (_root_.hammingDist (solverWordFixed PT hPT hm i a.1)
        (internalWord PT hPT i a.1) : ℝ) ≤ 1 := by exact_mod_cast hshift
    change (_root_.hammingDist ((clusterSolver PT hPT hm i).loc r)
      (solverWordFixed PT hPT hm i a.1) : ℝ) ≤ 10 * κ.ρ * (PT.tiling.P i).h at hnear
    linarith

theorem group_consultation_scope_subset_core {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) {g : ClusterGroupIndex PT}
    (hg : g ∈ clusterCoreGroups PT hPT hm a) :
    clusterConsultationScope PT hPT hm {groupConsultation g} ⊆
      coreRecordFootprint PT hPT hm a := by
  obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp hg
  subst g
  have hparts := (Finset.mem_filter.mp hb).2
  let i := patchAt PT hPT b.1
  let S := clusterSolver PT hPT hm i
  let z := solverWordFixed PT hPT hm i b.1
  let g := S.groupOf z
  have hpatch : patchAt PT hPT a.1 = i := hparts.2.symm
  have hz : z ∈ groupFiber g := S.groupOf_spec z (solver_word_odd_fixed PT hPT hm i b)
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hz
  have hcenter : _root_.hammingDist z g.1 = 1 := by rw [← hl]; exact flip_dist_one _ _
  have hraw : _root_.hammingDist z (internalWord PT hPT i b.1) ≤ 1 :=
    solver_word_raw_dist_le_one PT hPT hm i b.1
  have hrawCenter : _root_.hammingDist (internalWord PT hPT i b.1) g.1 ≤ 2 := by
    have ht := _root_.hammingDist_triangle (internalWord PT hPT i b.1) z g.1
    rw [hd_comm (internalWord PT hPT i b.1) z] at ht
    omega
  have haCenter : _root_.hammingDist (internalWord PT hPT i a.1) g.1 ≤ 3 := by
    have hab := internal_dist_le PT hPT i a.1 b.1
    have hadj := adjacent_dist hparts.1
    have ht := _root_.hammingDist_triangle (internalWord PT hPT i a.1)
      (internalWord PT hPT i b.1) g.1
    omega
  rintro ⟨s, r⟩ hr
  obtain ⟨c, hc, e, hnear⟩ := (Finset.mem_filter.mp hr).2
  have hc' : c = groupConsultation (clusterGroupIndexAt PT hPT hm b) := Finset.mem_singleton.mp hc
  subst c
  change clusterSliceAt PT hPT b.1 = s at e
  subst s
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, hpatch, ?_, ?_⟩
  · have ho := outside_dist_le PT hPT i a.1 b.1
    have hadj := adjacent_dist hparts.1
    have hor : _root_.hammingDist (outsideWord PT hPT i a.1) (outsideWord PT hPT i b.1) ≤ 1 := by omega
    exact_mod_cast hor
  · change (_root_.hammingDist (internalWord PT hPT i a.1) (S.loc r) : ℝ) ≤
      10 * κ.ρ * (PT.tiling.P i).h + 3
    change (_root_.hammingDist (S.loc r) g.1 : ℝ) ≤ 10 * κ.ρ * (PT.tiling.P i).h at hnear
    have ht := _root_.hammingDist_triangle (internalWord PT hPT i a.1) g.1 (S.loc r)
    have htR : (_root_.hammingDist (internalWord PT hPT i a.1) (S.loc r) : ℝ) ≤
      _root_.hammingDist (internalWord PT hPT i a.1) g.1 + _root_.hammingDist g.1 (S.loc r) := by
      exact_mod_cast ht
    rw [hd_comm g.1 (S.loc r)] at htR
    have hcenterR : (_root_.hammingDist (internalWord PT hPT i a.1) g.1 : ℝ) ≤ 3 := by
      exact_mod_cast haCenter
    linarith

noncomputable def coreConsultations {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) : Finset (ClusterConsultation PT) :=
  {rowConsultation PT hPT hm a} ∪
    (clusterCoreGroups PT hPT hm a).image groupConsultation

theorem core_consultations_scope_subset {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) :
    clusterConsultationScope PT hPT hm (coreConsultations PT hPT hm a) ⊆
      coreRecordFootprint PT hPT hm a := by
  intro r hr
  obtain ⟨c, hc, e, hnear⟩ := (Finset.mem_filter.mp hr).2
  rcases Finset.mem_union.mp hc with hc | hc
  · apply row_consultation_scope_subset_core PT hPT hm a
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hc, e, hnear⟩
  · obtain ⟨g, hg, hgc⟩ := Finset.mem_image.mp hc
    apply group_consultation_scope_subset_core PT hPT hm a hg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, c,
      Finset.mem_singleton.mpr hgc.symm, e, hnear⟩

noncomputable def internalOddNeighbour {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    (l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h) : OddPosition T k :=
  ⟨flipPos a.1 ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
    by have := clusterHeight_le PT hPT (patchAt PT hPT a.1); have := l.isLt; omega⟩,
   by
    intro h
    exact (evenRole_flipPos _ _).mp h a.2⟩

theorem internal_word_query_eq_odd {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h) :
    wordAtOdd PT hPT hm (internalOddNeighbour PT hPT a l) =
      ⟨clusterSliceAt PT hPT a.1, flipPos (clusterCenterRole PT hPT hm a).1 l⟩ := by
  apply Sigma.ext
  · exact Lane_q_s15_c2.clusterSliceAt_flip_internal PT hPT a.1 l
  · exact Lane_q_s15_c2.solverWordAt_flip_internal_heq PT hPT hm a l

theorem row_word_group_mem_core {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) {c : ClusterConsultation PT}
    (hc : c ∈ rowWordQueries PT hPT hm a) : wordGroup PT hPT hm c ∈ clusterCoreGroups PT hPT hm a := by
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hc
  rw [← hl, ← internal_word_query_eq_odd PT hPT hm a l]
  have hslice := Lane_q_s15_c2.clusterSliceAt_flip_internal PT hPT a.1 l
  have hpatch := congrArg Sigma.fst hslice
  apply Lane_q_s15_c2.clusterGroupIndexAt_mem_coreGroups
  · change _root_.hammingDist a.1 (internalOddNeighbour PT hPT a l).1 = 1
    rw [hd_comm]
    exact flip_dist_one _ _
  · exact hpatch

theorem kept_word_groups_core_or_crossing {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (M : ClusterMask PT) {g : ClusterGroupIndex PT}
    (hg : g ∈ (keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm)) :
    (∃ r ∈ clusterKeptRows M, g ∈ clusterCoreGroups PT hPT hm (M.positions r)) ∨
      (∃ q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins,
        g = clusterGroupIndexAt PT hPT hm q.2) := by
  obtain ⟨c, hc, hcg⟩ := Finset.mem_image.mp hg
  subst g
  rcases Finset.mem_union.mp hc with hc | hc
  · rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨r, hr, hcr⟩ := Finset.mem_biUnion.mp hc
      exact Or.inl ⟨r, hr, row_word_group_mem_core PT hPT hm (M.positions r) hcr⟩
    · obtain ⟨b, hb, hbc⟩ := Finset.mem_image.mp hc
      obtain ⟨r, hr, hbr⟩ := Finset.mem_biUnion.mp hb
      rw [← hbc]
      have hbparts := (Finset.mem_filter.mp hbr).2
      exact Or.inl ⟨r, hr, Lane_q_s15_c2.clusterGroupIndexAt_mem_coreGroups
        (M.positions r) b hbparts.1 hbparts.2.1⟩
  · obtain ⟨q, hq, hqc⟩ := Finset.mem_image.mp hc
    rw [← hqc]
    exact Or.inr ⟨q, hq, rfl⟩

theorem core_group_patch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) {g : ClusterGroupIndex PT}
    (hg : g ∈ clusterCoreGroups PT hPT hm a) : g.1.1 = patchAt PT hPT a.1 := by
  obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp hg
  rw [← hbg]
  exact (Finset.mem_filter.mp hb).2.2

theorem allowed_crossing_group_patch_ne {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    {q : Fin (T.S.n k) × OddPosition T k} (hq : q ∈ clusterAllowedCrossings PT hPT M) :
    (clusterGroupIndexAt PT hPT hm q.2).1.1 ≠ i := by
  have hcross := (Finset.mem_filter.mp hq).2.2.2
  have hpatch := Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 q.1)
  have hne := (Finset.mem_filter.mp hcross).2.2
  change patchAt PT hPT q.2.1 ≠ i
  simpa only [hpatch] using hne

theorem core_bin_removed_groups_not_read {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hradius : (6 : ℝ) ≤ 100 * κ.ρ * (PT.tiling.P i).h)
    {r : Fin (T.S.n k)} (hr : r ∈ M.coreBins) {g : ClusterGroupIndex PT}
    (hg : g ∈ clusterCoreGroups PT hPT hm (M.positions r)) :
    g ∉ (keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm) := by
  intro hread
  have hrg : r ∉ M.geometric := fun h => Finset.disjoint_left.mp hM.2.2.1 h hr
  rcases kept_word_groups_core_or_crossing PT hPT hm M hread with ⟨t, ht, hgt⟩ | ⟨q, hq, hqg⟩
  · have htnot := (Finset.mem_sdiff.mp ht).2
    have htg : t ∉ M.geometric := fun h => htnot (Finset.mem_union_left _ h)
    have htr : r ≠ t := by
      intro heq
      subst t
      exact htnot (Finset.mem_union_right _ hr)
    exact Finset.disjoint_left.mp
      (geometrically_retained_core_groups_disjoint PT hPT hm i M hM hradius hrg htg htr) hg hgt
  · have hgpatch : g.1.1 = i := (core_group_patch PT hPT hm _ hg).trans
      (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r))
    rw [hqg] at hgpatch
    exact allowed_crossing_group_patch_ne PT hPT hm i M hM (Finset.mem_sdiff.mp hq).1 hgpatch

theorem crossing_bin_removed_group_not_read {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (M : ClusterMask PT) (hM : ClusterMaskGeometry PT hPT i M)
    (hwidth : ∀ j, ((PT.tiling.P j).h : ℝ) + 2 ≤ (T.S.n k : ℝ) ^ (2 * κ.ι))
    {q : Fin (T.S.n k) × OddPosition T k} (hq : q ∈ M.crossingBins) :
    clusterGroupIndexAt PT hPT hm q.2 ∉
      (keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm) := by
  intro hread
  have hallowed := hM.2.2.2 hq
  rcases kept_word_groups_core_or_crossing PT hPT hm M hread with ⟨r, hr, hgr⟩ | ⟨p, hp, hpg⟩
  · have hgpatch := (core_group_patch PT hPT hm _ hgr).trans
      (Lane_q_s15_c2.patchAt_eq_of_evenPatchPosition hPT (hM.1 r))
    exact allowed_crossing_group_patch_ne PT hPT hm i M hM hallowed hgpatch
  · have hs := congrArg Sigma.fst hpg
    have hqp : q = p := allowed_crossing_slices_injective PT hPT M hwidth hallowed
      (Finset.mem_sdiff.mp hp).1 hs
    subst p
    exact (Finset.mem_sdiff.mp hp).2 hq

theorem kept_label_integral_skip_group {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT)
    (W : ClusterHistory PT hPT hm) {g : ClusterGroupIndex PT}
    (hg : g ∉ (keptWordQueries PT hPT hm M).image (wordGroup PT hPT hm))
    (B : ClusterBinAssignment PT) (D : clusterBinType g) :
    (clusterIndependentLabelKernel PT hPT hm W (Function.update B g D)).E
      (clusterKeptProduct PT hPT hm i x M W) =
    (clusterIndependentLabelKernel PT hPT hm W B).E (clusterKeptProduct PT hPT hm i x M W) := by
  apply kept_label_integral_bin_depends PT hPT hm i x M W
  intro g' hg'
  apply Function.update_of_ne
  exact fun heq => hg (heq ▸ hg')

theorem slice_eq_of_patch_and_outside {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (v w : Position T k)
    (hp : patchAt PT hPT v = patchAt PT hPT w)
    (ho : HEq (outsideWord PT hPT (patchAt PT hPT v) v)
      (outsideWord PT hPT (patchAt PT hPT w) w)) :
    clusterSliceAt PT hPT v = clusterSliceAt PT hPT w := by
  apply Sigma.ext hp
  apply (Subtype.heq_iff_coe_heq
    (congrArg (fun i : Fin PT.tiling.m => CubeVertex (T.S.n k - (PT.tiling.P i).h)) hp)
    (dependent_heq (fun i : Fin PT.tiling.m =>
      fun o : CubeVertex (T.S.n k - (PT.tiling.P i).h) =>
        ∀ j : Fin (T.S.n k - (PT.tiling.P i).h), j.val < (PT.tiling.P i).ℓ →
          o j = PT.tiling.w i ⟨j.val, by have := j.isLt; omega⟩) hp)).2
  exact ho

theorem bulk_flip_coordinate_outside {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k)
    {b : OddPosition T k} (hb : b ∈ clusterBulkNeighbours PT hPT a)
    {c : Fin (T.S.n k)} (hc : b.1 = flipPos a.1 c) :
    c.val < T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h := by
  have hparts := (Finset.mem_filter.mp hb).2
  by_contra hge
  apply hparts.2.2
  apply slice_eq_of_patch_and_outside PT hPT b.1 a.1 hparts.2.1
  apply HEq.trans (dependent_heq (fun i => outsideWord PT hPT i b.1) hparts.2.1)
  apply heq_of_eq
  funext j
  have hjc : (⟨j.val, by have := j.isLt; omega⟩ : Fin (T.S.n k)) ≠ c := by
    intro h
    have hv := congrArg Fin.val h
    have hj := j.isLt
    simp only [Fin.val_mk] at hv
    omega
  simp only [outsideWord, hc, flipPos]
  exact Function.update_of_ne hjc _ _

theorem bulk_slices_injective {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : EvenPosition T k) :
    Set.InjOn (fun b : OddPosition T k => clusterSliceAt PT hPT b.1)
      (clusterBulkNeighbours PT hPT a) := by
  intro b hb b' hb' hs
  have hp := (Finset.mem_filter.mp hb).2
  have hp' := (Finset.mem_filter.mp hb').2
  obtain ⟨c, hc⟩ := adjacent_eq_flip hp.1
  obtain ⟨d, hd⟩ := adjacent_eq_flip hp'.1
  have hcsmall := bulk_flip_coordinate_outside PT hPT a hb hc
  have hout := same_slice_outside_eq_on_patch PT hPT (patchAt PT hPT a.1) b.1 b'.1
    hp.2.1 hp'.2.1 hs
  have hcd : c = d := by
    by_contra hne
    have heq := congrFun hout ⟨c.val, hcsmall⟩
    have hidx : (⟨c.val, by have := hcsmall; omega⟩ : Fin (T.S.n k)) = c := rfl
    change b.1 c = b'.1 c at heq
    rw [hc, hd] at heq
    cases ha : a.1 c <;> simp [flipPos, hne, ha] at heq
  apply Subtype.ext
  rw [hc, hd, hcd]

end HypercubeRamsey.Lane_sol_s15_transfer
