import HypercubeRamsey.S18.Nodes_sol_split_d18l_sol_d18l_cal

namespace HypercubeRamsey.S18.Lane_sol_d18l_cal
open Classical
open scoped BigOperators
open S16.Lane_q_s16_comp2
set_option backward.isDefEq.respectTransparency false

/-- A cylinder comparison on all finite scopes compares every nonnegative
test of an injectively indexed query family. -/
theorem query_projection_upper {A R Y : Type*}
    [Fintype A] [Fintype R] [DecidableEq R] [Fintype Y] [DecidableEq Y]
    (Q : FinLaw (R → Y)) (P : R → FinLaw Y) (i : A → R)
    (hi : Function.Injective i) (y0 : Y) (r : ℝ)
    (hQ : ∀ ys : R → Y,
      Q.pr (fun x => ∀ j ∈ Finset.univ.image i, x j = ys j) ≤
        Real.exp (r * (Finset.univ.image i).card) *
          ∏ j ∈ Finset.univ.image i, (P j).w (ys j))
    (f : (A → Y) → ℝ) (hf : ∀ ys, 0 ≤ f ys) :
    Q.E (fun ys => f (fun a => ys (i a))) ≤
      Real.exp (r * Fintype.card A) *
        (FinLaw.pi fun a => P (i a)).E f := by
  classical
  apply expect_map_le Q (fun ys a => ys (i a)) (FinLaw.pi fun a => P (i a))
    (Real.exp (r * Fintype.card A)) f hf
  intro ys
  let S := Finset.univ.image i
  let extend : R → Y := fun j =>
    if h : ∃ a, i a = j then ys h.choose else y0
  have hext (a : A) : extend (i a) = ys a := by
    have ha : ∃ a', i a' = i a := ⟨a, rfl⟩
    simp only [extend, dif_pos ha]
    rw [hi ha.choose_spec]
  have hpred (x : R → Y) :
      (fun a => x (i a)) = ys ↔ ∀ j ∈ S, x j = extend j := by
    constructor
    · intro hx j hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      rw [hext]
      exact congrFun hx a
    · intro hx
      funext a
      simpa only [hext] using hx (i a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  have h := hQ extend
  change Q.pr (fun x => ∀ j ∈ S, x j = extend j) ≤
    Real.exp (r * S.card) * ∏ j ∈ S, (P j).w (extend j) at h
  have hprob : Q.pr (fun x => (fun a => x (i a)) = ys) =
      Q.pr (fun x => ∀ j ∈ S, x j = extend j) := by
    congr 1
    funext x
    exact propext (hpred x)
  rw [hprob]
  have hcard : S.card = Fintype.card A := by
    rw [Finset.card_image_of_injective _ hi]
    exact Finset.card_univ
  have hprod : (∏ j ∈ S, (P j).w (extend j)) =
      (FinLaw.pi fun a => P (i a)).w ys := by
    dsimp [S]
    rw [Finset.prod_image hi.injOn]
    simp only [hext, FinLaw.pi]
  simpa only [hcard, hprod] using h

private theorem flip_dist_le_one {n : ℕ} (z : CubePos n) (j : Fin n) :
    hammingDist (flipPos z j) z ≤ 1 := by
  calc
    _ ≤ ({j} : Finset (Fin n)).card := by
      apply Finset.card_le_card
      intro l hl
      have hd := (Finset.mem_filter.mp hl).2
      by_contra hn
      have hne : l ≠ j := by simpa using hn
      simp [flipPos, hne] at hd
    _ = 1 := by simp

/-- A word embedding preserving coordinate flips cannot increase Hamming
distance. This transports primitive consultation radii to physical words. -/
theorem flip_embedding_distance {h n : ℕ} (E : CubePos h → CubePos n)
    (axis : Fin h → Fin n)
    (hflip : ∀ z j, E (flipPos z j) = flipPos (E z) (axis j)) (z w : CubePos h) :
    hammingDist (E z) (E w) ≤ hammingDist z w := by
  have haux : ∀ d : ℕ, ∀ z w : CubePos h, hammingDist z w = d →
      hammingDist (E z) (E w) ≤ d := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro z w hd
      by_cases he : z = w
      · subst w; simp [HypercubeRamsey.hammingDist]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp he
      let S := Finset.univ.filter fun l => z l ≠ w l
      have hjS : j ∈ S := by simp [S, hj]
      have hset : (Finset.univ.filter fun l => (flipPos z j) l ≠ w l) = S.erase j := by
        ext l
        by_cases hl : l = j
        · subst l
          cases hz : z j <;> cases hw : w j <;> simp_all [S, flipPos]
        · simp [S, flipPos, hl]
      have hd' : hammingDist (flipPos z j) w + 1 = d := by
        change (Finset.univ.filter fun l => (flipPos z j) l ≠ w l).card + 1 = d
        rw [hset, Finset.card_erase_add_one hjS]
        exact hd
      have hsmall : hammingDist (flipPos z j) w < d := by omega
      have hrec := ih _ hsmall (flipPos z j) w rfl
      have hstep : hammingDist (E z) (E (flipPos z j)) ≤ 1 := by
        rw [hflip]
        change _root_.hammingDist (E z) (flipPos (E z) (axis j)) ≤ 1
        rw [_root_.hammingDist_comm]
        exact flip_dist_le_one _ _
      calc
        hammingDist (E z) (E w) ≤
            hammingDist (E z) (E (flipPos z j)) + hammingDist (E (flipPos z j)) (E w) :=
          hammingDist_triangle _ _ _
        _ ≤ 1 + hammingDist (flipPos z j) w := Nat.add_le_add hstep hrec
        _ = d := by omega
  exact haux _ z w rfl

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {G : LowGeom PT}
open S16 S16.Lane_sol_fix2_s16

/-- Retain the exact fresh-law readout when comparing the calibrated
bin and label stages. -/
theorem query_stage_readout {F : FreshCell G} (Cal : FreshLabelCalibration F)
    (C : G.Cell) (pool : F.Pool C) (ht : F.typical C pool) {A : Type*} [Fintype A]
    (r : A → OddCellRole G C) (f : A → Fin (T.S.N k) → ℝ) :
    (F.fresh C pool).E (fun s => ∏ a, f a (F.label C s (r a).1)) =
      (Cal.gatedHistory C pool).E (fun W => (Cal.binSampler C pool W).E (fun bins =>
        (Cal.labelSampler C pool W bins).E (fun ys => ∏ a, f a (ys (r a))))) := by
  classical
  rw [Cal.fresh_eq C pool ht, S16.Lane_q_s16_comp2.map_expect]
  calc
    _ = (FinLaw.bind (Cal.gatedHistory C pool) fun W =>
        FinLaw.bind (Cal.binSampler C pool W) (Cal.labelSampler C pool W)).E
          (fun ω => ∏ a, f a (ω.2.2 (r a))) := by
      apply expect_congr_of_support
      intro ω hω
      have hweights : (Cal.gatedHistory C pool).w ω.1 *
          ((Cal.binSampler C pool ω.1).w ω.2.1 *
            (Cal.labelSampler C pool ω.1 ω.2.1).w ω.2.2) ≠ 0 := hω
      obtain ⟨hW, hrest⟩ := mul_ne_zero_iff.mp hweights
      obtain ⟨hbin, hys⟩ := mul_ne_zero_iff.mp hrest
      apply Finset.prod_congr rfl
      intro a _
      rw [Cal.label_eq C pool ω.1 ω.2.1 ω.2.2 (r a) ht hW hbin hys]
    _ = _ := by simp_rw [bind_expect]

theorem zero_queries {hPT : PT.Valid} (D : LateData hPT) (C : D.geom.Cell)
    (odd : Fin 0 → Pos T k) (f : Fin 0 → Fin (T.S.N k) → ℝ) :
    (D.cellPoolLaw C).E (fun P => if D.fresh.typical C P then
      (D.fresh.fresh C P).E (fun s => ∏ a, f a (D.fresh.label C s (odd a))) else 0) ≤
      Real.exp (0.002 * (0 : ℕ)) *
        ∏ a, ((∑ y, (PT.πraw (D.geom.patchOf (odd a))).w y * f a y) +
          Real.rpow (T.S.n k : ℝ) (-((κ.Ac : ℝ) - 3))) := by
  simp only [Finset.univ_eq_empty, Finset.prod_empty, Nat.cast_zero,
    mul_zero, Real.exp_zero, mul_one]
  calc
    _ ≤ (D.cellPoolLaw C).E (fun _ => 1) := by
      apply expect_le
      intro P
      split_ifs
      · simp [FinLaw.E, FinLaw.sum_one]
      · norm_num
    _ = 1 := by simp [FinLaw.E, FinLaw.sum_one]

/-- Two roles of one physical projected group are one-flip neighbours of
the same centre, so their distance is at most two. -/
theorem same_group_distance (R : CellRawData G) (hR : R.SourceValid)
    (hc : PT.tiling.mode.isCluster) (C : G.Cell) (r t : OddCellRole G C)
    (hrt : R.groupOf C r = R.groupOf C t) : hammingDist r.1 t.1 ≤ 2 := by
  rcases hR with ⟨hm, hUniform, hSource⟩ | ⟨hd, hSource⟩
  · obtain ⟨S, hS, records, groups, hLaw, hPass, hGroup, hQ, hTrim, hU, hPrior⟩ := hSource C
    let zr := (R.cellWords C).symm ⟨r.1, r.2.1⟩
    let zt := (R.cellWords C).symm ⟨t.1, t.2.1⟩
    have er : (R.cellWords C zr).1 = r.1 :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply _)
    have et : (R.cellWords C zt).1 = t.1 :=
      congrArg Subtype.val ((R.cellWords C).apply_symm_apply _)
    have hor : ¬ IsEvenRole (R.cellWords C zr).1 := by rw [er]; exact r.2.2
    have hot : ¬ IsEvenRole (R.cellWords C zt).1 := by rw [et]; exact t.2.2
    have gr := hGroup zr.1 zr.2 hor
    have gt := hGroup zt.1 zt.2 hot
    have rr : (⟨(R.cellWords C zr).1, (R.cellWords C zr).2, hor⟩ : OddCellRole G C) = r :=
      Subtype.ext er
    have tt : (⟨(R.cellWords C zt).1, (R.cellWords C zt).2, hot⟩ : OddCellRole G C) = t :=
      Subtype.ext et
    rw [rr] at gr
    rw [tt] at gt
    have hpair : (zr.1, S.groupOf zr.2) = (zt.1, S.groupOf zt.2) :=
      groups.injective (gr.symm.trans (hrt.trans gt))
    have hslice : zr.1 = zt.1 := congrArg
      (fun x : R.Slice C × Group PT.tiling (G.cellPatch C) => x.1) hpair
    have hgp : S.groupOf zr.2 = S.groupOf zt.2 := congrArg Prod.snd hpair
    have ozr : ¬ IsEvenRole zr.2 := fun h => hor ((R.word_parity hc C zr.1 zr.2).mpr h)
    have ozt : ¬ IsEvenRole zt.2 := fun h => hot ((R.word_parity hc C zt.1 zt.2).mpr h)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (S.groupOf_spec zr.2 ozr)
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp (S.groupOf_spec zt.2 ozt)
    have hrflip : r.1 = flipPos (R.cellWords C (zr.1, (S.groupOf zr.2).1)).1 (R.axis C j) := by
      calc
        r.1 = (R.cellWords C (zr.1, zr.2)).1 := er.symm
        _ = (R.cellWords C (zr.1, flipPos (S.groupOf zr.2).1 j)).1 :=
          congrArg (fun z => (R.cellWords C (zr.1, z)).1) hj.symm
        _ = _ := R.word_flip C _ _ _
    have htflip : t.1 = flipPos (R.cellWords C (zr.1, (S.groupOf zr.2).1)).1 (R.axis C l) := by
      calc
        t.1 = (R.cellWords C (zt.1, zt.2)).1 := et.symm
        _ = (R.cellWords C (zt.1, flipPos (S.groupOf zt.2).1 l)).1 :=
          congrArg (fun z => (R.cellWords C (zt.1, z)).1) hl.symm
        _ = flipPos (R.cellWords C (zt.1, (S.groupOf zt.2).1)).1 (R.axis C l) :=
          R.word_flip C _ _ _
        _ = _ := by rw [← hslice, ← hgp]
    rw [hrflip, htflip]
    exact (hammingDist_triangle_right _ _ _).trans
      (Nat.add_le_add (flip_dist_le_one _ _) (flip_dist_le_one _ _))
  · exact (hd hc).elim

/-- The repaired height margin excludes shared projected groups from the
distance-only query domain. -/
theorem query_groups_injective (hκ : κ.Admissible) (hT : LateThresholds κ)
    (hPT : PT.Valid) (R : CellRawData G) (hR : R.SourceValid)
    (hc : PT.tiling.mode.isCluster) (hlow : PT.tiling.mode.isLow)
    (C : G.Cell) {A : Type*} (r : A → OddCellRole G C)
    (hSep : ∀ a b, a ≠ b → 50 * κ.ρ * (PT.tiling.P (G.cellPatch C)).h <
      (hammingDist (r a).1 (r b).1 : ℝ)) :
    Function.Injective (fun a => R.groupOf C (r a)) := by
  have hm : PT.tiling.mode = .lowCluster := by
    cases hm : PT.tiling.mode <;> simp_all [Mode.isLow, Mode.isCluster]
  have hMargin := patch_threshold hκ hT hPT hm (G.cellPatch C)
  have hρh : 0 ≤ κ.ρ * (PT.tiling.P (G.cellPatch C)).h :=
    mul_nonneg hκ.ρ_rng.1.le (Nat.cast_nonneg _)
  intro a b hab
  by_contra hne
  have hdist : (hammingDist (r a).1 (r b).1 : ℝ) ≤ 2 := by
    exact_mod_cast same_group_distance R hR hc C (r a) (r b) hab
  have hs := hSep a b hne
  nlinarith

/-- Separated observed words have disjoint primitive consultation balls,
including both one-flip shifts from observations to group centres. -/
theorem consultations_disjoint {R : Type*} [Fintype R]
    (i : Fin PT.tiling.m) (loc : R → IWord PT.tiling i)
    (E : IWord PT.tiling i → Pos T k)
    (axis : Fin (PT.tiling.P i).h → Fin (T.S.n k))
    (hflip : ∀ z j, E (flipPos z j) = flipPos (E z) (axis j))
    (u v c d : IWord PT.tiling i)
    (hu : hammingDist u c ≤ 1) (hv : hammingDist v d ≤ 1)
    (hMargin : 2 < 20 * κ.ρ * (PT.tiling.P i).h)
    (hSep : 50 * κ.ρ * (PT.tiling.P i).h < (hammingDist (E u) (E v) : ℝ)) :
    Disjoint (recordNear loc c) (recordNear loc d) := by
  classical
  apply Finset.disjoint_left.mpr
  intro r hr hs
  have hrc := (Finset.mem_filter.mp hr).2
  have hrd := (Finset.mem_filter.mp hs).2
  have hcd : (hammingDist c d : ℝ) ≤
      (hammingDist (loc r) c : ℝ) + (hammingDist (loc r) d : ℝ) := by
    exact_mod_cast _root_.hammingDist_triangle_left c d (loc r)
  have hucd : (hammingDist u d : ℝ) ≤
      (hammingDist u c : ℝ) + (hammingDist c d : ℝ) := by
    exact_mod_cast hammingDist_triangle u c d
  have hudv : (hammingDist u v : ℝ) ≤
      (hammingDist u d : ℝ) + (hammingDist v d : ℝ) := by
    exact_mod_cast _root_.hammingDist_triangle_right u v d
  have huR : (hammingDist u c : ℝ) ≤ 1 := by exact_mod_cast hu
  have hvR : (hammingDist v d : ℝ) ≤ 1 := by exact_mod_cast hv
  have hE : (hammingDist (E u) (E v) : ℝ) ≤ (hammingDist u v : ℝ) := by
    exact_mod_cast flip_embedding_distance E axis hflip u v
  simp only [HypercubeRamsey.hammingDist, _root_.hammingDist] at hrc hrd hcd hucd hudv huR hvR hE hSep
  nlinarith

end HypercubeRamsey.S18.Lane_sol_d18l_cal
