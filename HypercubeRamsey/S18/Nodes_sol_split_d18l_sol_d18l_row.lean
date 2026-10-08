import HypercubeRamsey.S18.Nodes_sol_s18_dl
import HypercubeRamsey.S18.PaletteRows

namespace HypercubeRamsey.S18.Lane_sol_d18l_row

open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

/-- The centered pair correlation is unchanged when both hits are complemented. -/
theorem corr_colour_independent {N : ℕ} (E : Fin N → Fin N → Prop)
    (c : Colour) (π : Fin N → ℝ) (x z : Fin N) :
    corr E true π x z = corr E c π x z := by
  cases c with
  | true => rfl
  | false =>
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hx : E x y <;> by_cases hz : E z y <;>
        norm_num [fv, hit, Hits, hx, hz]

/-- Different flip coordinates give different neighbours. -/
theorem flip_injective {n : ℕ} (v : CubePos n) :
    Function.Injective (fun a => flipPos v a) := by
  intro a b hab
  by_contra hne
  have h := congrFun hab a
  simp only [flipPos, Function.update_self, Function.update_of_ne hne] at h
  cases hv : v a <;> simp [hv] at h

theorem external_early_image (D : LateData hPT)
    (physical : PhysicalFreshCertificate D.geom D.fresh) (v : Pos T k) :
    (Lane_sol_s18_dl.physical_list_context hPT D.low_mode physical).externalEarly v =
      (D.externalEarly v).image (fun a => flipPos v a) := by
  ext b
  simp only [ListGateContext.externalEarly, LateData.externalEarly,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨hclass, a, ha, rfl⟩
    exact ⟨a, ⟨ha, hclass⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hclass⟩, rfl⟩
    exact ⟨hclass, a, ha, rfl⟩

theorem external_pair_product (D : LateData hPT)
    (physical : PhysicalFreshCertificate D.geom D.fresh)
    (v : Pos T k) (x z : Fin (T.S.N k)) :
    (∏ a ∈ D.externalEarly v,
      externalPairFactor (PT := PT) (D.geom.patchOf (flipPos v a)) x z) =
    ∏ w ∈ (Lane_sol_s18_dl.physical_list_context hPT D.low_mode physical).externalEarly v,
      externalPairFactor (PT := PT) (D.geom.patchOf w) x z := by
  rw [external_early_image D physical v]
  rw [Finset.prod_image]
  intro a ha b hb hab
  exact flip_injective v hab

/-- Internal validity supplies the cleaned shape; the retained-mass bridge
supplies the direct-mode size clause for the same chosen corner. -/
theorem clean_initial_prior (D : LateData hPT)
    (physical : PhysicalFreshCertificate D.geom D.fresh)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.internalValid v s) :
    (Lane_sol_s18_dl.physical_list_context hPT D.low_mode physical).CleanInitialPrior
      v (D.sigma v s) := by
  dsimp only [ListGateContext.CleanInitialPrior, Lane_sol_s18_dl.physical_list_context]
  rcases hvalid with ⟨hnonneg, hnorm, hshape, hsupport, hhits⟩
  refine ⟨hnonneg, hnorm, ?_⟩
  by_cases hc : PT.tiling.mode.isCluster
  · obtain ⟨q, hq, hqSupport⟩ := hsupport
    refine ⟨q, hq, ?_, ?_, ?_⟩
    · intro x hx
      by_contra hnot
      exact hx (hqSupport x hnot)
    · intro _
      simpa only [if_pos hc] using hshape
    · intro hn
      exact (hn hc).elim
  · obtain ⟨q, hq, hqUniform⟩ := (show ∃ q ∈ PT.activeVertices, ∀ x,
        D.sigma v s x = if x ∈ PT.mesh.corner q (D.geom.patchOf v) then
          1 / ((PT.mesh.corner q (D.geom.patchOf v)).card : ℝ) else 0 by
        simpa only [if_neg hc] using hshape)
    refine ⟨q, hq, ?_, ?_, ?_⟩
    · intro x hx
      by_contra hnot
      exact hx (by rw [hqUniform x, if_neg hnot])
    · intro hcluster
      exact (hc hcluster).elim
    · intro _
      exact ⟨Lane_sol_fix_corner.active_corner_card_lower_waste hPT _ q hq, hqUniform⟩

/-- Only the supported own-cell readout is used to certify S17 provenance. -/
theorem valid_initial_prior (D : LateData hPT)
    (physical : PhysicalFreshCertificate D.geom D.fresh)
    (v : Pos T k) (s : Config D.fresh) (hvalid : D.internalValid v s)
    (P : D.fresh.Pool (D.geom.cellOf v))
    (ht : D.fresh.typical (D.geom.cellOf v) P)
    (hs : 0 < (D.fresh.fresh (D.geom.cellOf v) P).w (s (D.geom.cellOf v))) :
    (Lane_sol_s18_dl.physical_list_context hPT D.low_mode physical).ValidInitialPrior
      v (D.sigma v s) := by
  refine ⟨clean_initial_prior D physical v s hvalid, P, s (D.geom.cellOf v), ht, ?_,
    fun x => rfl⟩
  exact ⟨physical.fresh_spec.fresh_valid _ P _ ht hs, hs⟩

/-- Reindex an S17 pair-row estimate by the actual flip coordinates. -/
theorem palette_row_transport (D : LateData hPT)
    (physical : PhysicalFreshCertificate D.geom D.fresh)
    (hle : ∀ i, (PT.tiling.P i).h ≤ T.S.n k)
    (code : ∀ i, S17PaletteCode i (hle i))
    (colours : ∀ i, S17PaletteAssignment (code i))
    (hpalette : ∀ v, D.palette v =
      s17Palette (code (D.geom.patchOf v)) (colours (D.geom.patchOf v)) v)
    (hchi : ∀ i, D.chi i = s17Chi (code i)) (Krow : ℝ)
    (hrows : ∀ i, PalettePairRowBound
      (Lane_sol_s18_dl.physical_list_context hPT D.low_mode physical)
        i (hle i) (code i) (colours i) Krow) : PaletteRowInput D Krow := by
  intro v heven s hvalid P ht hs x hx
  have hprior := valid_initial_prior D physical v s hvalid P ht hs
  have hrow := hrows (D.geom.patchOf v) v (D.geom.patchOf_leaf v) heven
    (D.sigma v s) hprior x hx
  rw [hpalette v, hchi (D.geom.patchOf v)]
  calc
    _ = ∑ z ∈ s17Palette (code (D.geom.patchOf v)) (colours (D.geom.patchOf v)) v,
        (if |corr (T.S.E k) PT.tiling.c (PT.π (D.geom.patchOf v)).w x z| ≤ κ.ξ then
          D.sigma v s z * ∏ w ∈
            (Lane_sol_s18_dl.physical_list_context hPT D.low_mode physical).externalEarly v,
            externalPairFactor (PT := PT) (D.geom.patchOf w) x z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [LateData.nonconflict, pairCorr,
        corr_colour_independent (T.S.E k) PT.tiling.c,
        external_pair_product D physical v x z]
    _ ≤ _ := hrow

/-- The S16 star-location contract permits any even word as the site: it
does not select S17's canonical internal word. -/
theorem slice_star_location_rebase {G : LowGeom PT} {C : G.Cell} {v : Pos T k}
    {w : EvenRole PT.tiling (G.cellPatch C)}
    (loc : S16.SliceStarLocation G C v w)
    (w' : EvenRole PT.tiling (G.cellPatch C)) :
    Nonempty (S16.SliceStarLocation G C v w') := by
  let shift (z : IWord PT.tiling (G.cellPatch C)) :=
    fun j => Bool.xor (Bool.xor (z j) (w'.1 j)) (w.1 j)
  have hsite : shift w'.1 = w.1 := by
    funext j
    change Bool.xor (Bool.xor (w'.1 j) (w'.1 j)) (w.1 j) = w.1 j
    cases hw' : w'.1 j <;> cases hw : w.1 j <;> rfl
  have hflip (z : IWord PT.tiling (G.cellPatch C)) (j) :
      shift (flipPos z j) = flipPos (shift z) j := by
    funext a
    by_cases ha : a = j
    · subst a
      simp only [shift, flipPos, Function.update_self]
      cases hz : z j <;> cases hw' : w'.1 j <;> cases hw : w.1 j <;> rfl
    · simp [shift, flipPos, ha]
  exact ⟨{
    axis := loc.axis
    axis_injective := loc.axis_injective
    axes_eq := loc.axes_eq
    embed := fun z => loc.embed (shift z)
    site_eq := by rw [hsite]; exact loc.site_eq
    flip_eq := fun z j => by rw [hflip]; exact loc.flip_eq _ j
    outer_eq := fun z j hj => loc.outer_eq _ j hj }⟩

/-- In contrast, the S17 ordered-role condition selects at most one word. -/
theorem solver_role_matches_unique (D : ListGateContext κ T k PT) (v : Pos T k)
    (hle : (PT.tiling.P (D.G.patchOf v)).h ≤ T.S.n k)
    (e e' : EvenRole PT.tiling (D.G.patchOf v))
    (he : D.SolverRoleMatches v e) (he' : D.SolverRoleMatches v e') : e = e' := by
  apply Subtype.ext
  funext j
  exact (he hle j).trans (he' hle j).symm

/-- Proposed additional raw-data field. It fixes the internal order and
the translation by the parity of the outer word, before sampler transport. -/
def RawWordOrder {G : LowGeom PT} (R : S16.Lane_sol_fix2_s16.CellRawData G) : Prop :=
  PT.tiling.mode.isCluster → ∀ C s z
    (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (j : Fin (PT.tiling.P (G.cellPatch C)).h),
    z j = if ¬ IsEvenRole (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else
        (R.cellWords C (s, z)).1 l) ∧ j.val = 0
      then !((R.cellWords C (s, z)).1
        (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j))
      else (R.cellWords C (s, z)).1
        (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j)

private theorem role_matches_transport (D : ListGateContext κ T k PT)
    (v : Pos T k) (i : Fin PT.tiling.m) (e : EvenRole PT.tiling i)
    (hi : i = D.G.patchOf v)
    (h : ∀ (hle : (PT.tiling.P i).h ≤ T.S.n k) (j : Fin (PT.tiling.P i).h),
      e.1 j = if ¬ IsEvenRole (fun l : Fin (T.S.n k) =>
        if l ∈ PT.tiling.Icoord i then false else v l) ∧ j.val = 0
        then !(v (S16.Lane_q_s16_prod1.cellAxis i hle j))
        else v (S16.Lane_q_s16_prod1.cellAxis i hle j)) :
    D.SolverRoleMatches v (cast (by rw [hi]) e) := by
  subst i
  exact h

/-- The proposed field supplies exactly the ordered-role conjunct absent
from the current raw source interface. -/
theorem raw_word_order_solver_role {G : LowGeom PT}
    (R : S16.Lane_sol_fix2_s16.CellRawData G) (hOrder : RawWordOrder R)
    (hCluster : PT.tiling.mode.isCluster) (D : ListGateContext κ T k PT)
    (hG : D.G = G) (v : Pos T k) (C : G.Cell) (s : R.Slice C)
    (e : EvenRole PT.tiling (G.cellPatch C)) (hcell : G.cellOf v = C)
    (hsite : (R.cellWords C (s, e.1)).1 = v) :
    D.SolverRoleMatches v (cast (by rw [hG, ← G.cellOf_patch v, hcell]) e) := by
  subst hG
  apply role_matches_transport D v (D.G.cellPatch C) e
    (by rw [← D.G.cellOf_patch v, hcell])
  intro hle j
  simpa only [hsite] using hOrder hCluster C s e.1 hle j

/-- The single proposed field also determines the stored axis order;
no second ordering assumption is needed for internal neighbor labels. -/
theorem raw_word_order_axis {G : LowGeom PT}
    (R : S16.Lane_sol_fix2_s16.CellRawData G) (hOrder : RawWordOrder R)
    (hCluster : PT.tiling.mode.isCluster) (C : G.Cell) (s : R.Slice C)
    (z : IWord PT.tiling (G.cellPatch C))
    (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (j : Fin (PT.tiling.P (G.cellPatch C)).h) :
    R.axis C j = S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j := by
  by_contra hne
  have houter : (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else
        (R.cellWords C (s, flipPos z j)).1 l) =
      (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else
        (R.cellWords C (s, z)).1 l) := by
    funext l
    by_cases hl : l ∈ PT.tiling.Icoord (G.cellPatch C)
    · simp [hl]
    · simp only [ite_eq_right hl]
      exact (R.word_outer C s z (flipPos z j) l hl).symm
  have hbit : (R.cellWords C (s, flipPos z j)).1
      (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) =
      (R.cellWords C (s, z)).1
        (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) := by
    rw [R.word_flip]
    exact Function.update_of_ne (Ne.symm hne) _ _
  have hflip := hOrder hCluster C s (flipPos z j) hle j
  rw [houter, hbit] at hflip
  have hold := hOrder hCluster C s z hle j
  rw [← hold] at hflip
  simp only [flipPos, Function.update_self] at hflip
  cases hz : z j <;> simp [hz] at hflip

theorem raw_word_order_flip {G : LowGeom PT}
    (R : S16.Lane_sol_fix2_s16.CellRawData G) (hOrder : RawWordOrder R)
    (hCluster : PT.tiling.mode.isCluster) (C : G.Cell) (s : R.Slice C)
    (z : IWord PT.tiling (G.cellPatch C))
    (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (j : Fin (PT.tiling.P (G.cellPatch C)).h) :
    (R.cellWords C (s, flipPos z j)).1 =
      flipPos (R.cellWords C (s, z)).1
        (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) := by
  rw [R.word_flip, raw_word_order_axis R hOrder hCluster C s z hle j]

/-- The existing canonical constructor satisfies the proposed word order.
Keeping this identity in its output avoids reconstructing it from a free
slice embedding later. -/
theorem cluster_cell_words_order {G : LowGeom PT} (C : G.Cell)
    (whole : ∀ v, G.cellOf v = C → ∀ v',
      S16.CellData.sameSlice (G.cellPatch C) v v' → G.cellOf v' = C)
    (hle : (PT.tiling.P (G.cellPatch C)).h ≤ T.S.n k)
    (hpos : 0 < (PT.tiling.P (G.cellPatch C)).h)
    (s : S16.Lane_q_s16_prod1.ClusterCellSlice G C)
    (z : IWord PT.tiling (G.cellPatch C))
    (j : Fin (PT.tiling.P (G.cellPatch C)).h) :
    z j = if ¬ IsEvenRole (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else
        (S16.Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1 l)
      ∧ j.val = 0
      then !((S16.Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1
        (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j))
      else (S16.Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1
        (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) := by
  let v := (S16.Lane_q_s16_prod1.clusterCellWords C whole hle hpos (s, z)).1
  have houter : (fun l : Fin (T.S.n k) =>
      if l ∈ PT.tiling.Icoord (G.cellPatch C) then false else v l) = s.1 := by
    funext l
    by_cases hl : l ∈ PT.tiling.Icoord (G.cellPatch C)
    · simp only [ite_eq_left hl]
      exact (s.2.2 l hl).symm
    · simp [v, S16.Lane_q_s16_prod1.clusterCellWords,
        S16.Lane_q_s16_prod1.clusterCombine, hl]
  have hjmem : S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j ∈
      PT.tiling.Icoord (G.cellPatch C) := by
    rw [← S16.Lane_q_s16_prod1.cellAxis_image (G.cellPatch C) hle]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hbit : v (S16.Lane_q_s16_prod1.cellAxis (G.cellPatch C) hle j) =
      S16.Lane_q_s16_prod1.clusterShiftWord s z hpos j := by
    simp [v, S16.Lane_q_s16_prod1.clusterCellWords,
      S16.Lane_q_s16_prod1.clusterCombine, hjmem,
      S16.Lane_q_s16_prod1.cellAxisInv_cellAxis]
  change z j = if ¬ IsEvenRole _ ∧ j.val = 0 then !(v _) else v _
  rw [houter, hbit]
  by_cases hs : IsEvenRole s.1
  · simp [hs, S16.Lane_q_s16_prod1.clusterShiftWord]
  · by_cases hj : j.val = 0
    · have hj' : j = ⟨0, hpos⟩ := Fin.ext hj
      simp [hs, S16.Lane_q_s16_prod1.clusterShiftWord, flipPos, hj']
    · have hj' : j ≠ ⟨0, hpos⟩ := fun h => hj (congrArg Fin.val h)
      simp [hs, hj, S16.Lane_q_s16_prod1.clusterShiftWord, flipPos, hj']

/-- Even parity and flip preservation permit a different origin already
on a two-coordinate slice. The canonical translated word at the zero site
is zero, whereas this valid local star places the all-one word there. -/
theorem two_coordinate_origin_example :
    let translate : CubePos 2 → CubePos 2 := fun z => fun j => !(z j)
    let zero : CubePos 2 := fun _ => false
    let one : CubePos 2 := fun _ => true
    (∀ z, IsEvenRole (translate z) ↔ IsEvenRole z) ∧
    (∀ z j, translate (flipPos z j) = flipPos (translate z) j) ∧
    translate one = zero ∧ IsEvenRole one ∧ one ≠ zero := by
  classical
  dsimp only
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro z
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
    cases h0 : z 0 <;> cases h1 : z 1 <;>
      norm_num [IsEvenRole, huniv, Finset.filter_insert, Finset.filter_singleton, h0, h1]
  · intro z j
    funext a
    by_cases ha : a = j
    · subst a
      simp [flipPos]
    · simp [flipPos, ha]
  · norm_num [IsEvenRole]
  · intro h
    have h0 := congrFun h 0
    exact Bool.noConfusion h0

/-- Rebase to any other solver word while witnessing failure of S17's
ordered-role requirement. No conclusion about the pair-row estimate is used. -/
theorem noncanonical_slice_location (D : ListGateContext κ T k PT)
    (v : Pos T k) (hle : (PT.tiling.P (D.G.patchOf v)).h ≤ T.S.n k)
    (e e' : EvenRole PT.tiling (D.G.patchOf v)) (hne : e' ≠ e)
    (he : D.SolverRoleMatches v e)
    (loc : S16.SliceStarLocation D.G (D.G.cellOf v) v
      (cast (by rw [D.G.cellOf_patch]) e)) :
    Nonempty (S16.SliceStarLocation D.G (D.G.cellOf v) v
      (cast (by rw [D.G.cellOf_patch]) e')) ∧ ¬ D.SolverRoleMatches v e' := by
  refine ⟨slice_star_location_rebase loc _, ?_⟩
  intro he'
  exact hne (solver_role_matches_unique D v hle e' e he' he)

end HypercubeRamsey.S18.Lane_sol_d18l_row
