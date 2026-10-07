import HypercubeRamsey.S18.Locality_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem classOf_eq_some_iff (G : LowGeom PT) (b : Pos T k) (j : Fin G.r) :
    G.classOf b = some j ↔ ¬ IsEvenRole b ∧ G.syndrome b = (G.classEnum j).1 := by
  constructor
  · intro h
    unfold LowGeom.classOf at h
    split_ifs at h with hb
    · have he := Option.some.inj h
      refine ⟨hb.1, ?_⟩
      have hv := congrArg (fun q => (G.classEnum q).1) he
      simpa only [Equiv.apply_symm_apply] using hv
  · rintro ⟨hodd, hs⟩
    have hmem : G.syndrome b ∈ G.Lsub := hs ▸ (G.classEnum j).2
    have hb : ¬ IsEvenRole b ∧ G.syndrome b ∈ G.Lsub := ⟨hodd, hmem⟩
    simp only [LowGeom.classOf, dif_pos hb, Option.some.injEq]
    apply G.classEnum.injective
    apply Subtype.ext
    simpa only [Equiv.apply_symm_apply] using hs

/-- The linked physical certificate retains the exact syndrome fibre size.
It is available even though the flattened quantitative fields omit it. -/
theorem class_card_exact (D : LateData hPT) (j : Fin D.geom.r) :
    (D.encoding.base.classes j).card = 2 ^ (T.S.n k - 1) / 2 ^ D.geom.Hdim := by
  obtain ⟨p⟩ := D.l16_valid.physical
  have hsize : ∀ j : Fin D.geom.r,
      Fintype.card {b : Pos T k // ¬ IsEvenRole b ∧ D.geom.syndrome b = (D.geom.classEnum j).1} =
        2 ^ (T.S.n k - 1) / 2 ^ D.geom.Hdim := by
    have hp : ∀ j : Fin p.geometry.geom.r,
        Fintype.card {b : Pos T k // ¬ IsEvenRole b ∧
          p.geometry.geom.syndrome b = (p.geometry.geom.classEnum j).1} =
            2 ^ (T.S.n k - 1) / 2 ^ p.geometry.geom.Hdim := p.geometry.late_classes.class_size
    rw [p.geometry_eq] at hp
    exact hp
  let e : {b : Pos T k // b ∈ D.encoding.base.classes j} ≃
      {b : Pos T k // ¬ IsEvenRole b ∧ D.geom.syndrome b = (D.geom.classEnum j).1} :=
    Equiv.subtypeEquivRight fun b =>
      (D.encoding.base.class_of_spec b j).trans (classOf_eq_some_iff D.geom b j)
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).trans (hsize j)

theorem syndrome_group_size (D : LateData hPT) :
    T.S.n k ≤ 2 ^ D.geom.Hdim ∧ 2 ^ D.geom.Hdim < 2 * T.S.n k := by
  obtain ⟨p⟩ := D.l16_valid.physical
  have hp : T.S.n k ≤ 2 ^ p.geometry.geom.Hdim ∧
      2 ^ p.geometry.geom.Hdim < 2 * T.S.n k := p.geometry.late_classes.group_size
  rwa [p.geometry_eq] at hp

private theorem twice_dimension_le_halved_cube (n : ℕ) (hn : 6 ≤ n) :
    2 * n ≤ 2 ^ (n - 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have he : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [he, pow_succ]
    nlinarith

theorem class_card_pos (D : LateData hPT) (hn : 6 ≤ T.S.n k) (j : Fin D.geom.r) :
    0 < (D.encoding.base.classes j).card := by
  rw [class_card_exact]
  apply Nat.div_pos
  · exact (syndrome_group_size D).2.le.trans (twice_dimension_le_halved_cube _ hn)
  · positivity

theorem cube_size_le_class_card (D : LateData hPT) (hn : 6 ≤ T.S.n k) (j : Fin D.geom.r) :
    2 ^ T.S.n k ≤ 8 * T.S.n k * (D.encoding.base.classes j).card := by
  let L := (D.encoding.base.classes j).card
  let B := 2 ^ D.geom.Hdim
  have hL : 1 ≤ L := class_card_pos D hn j
  have hB : 0 < B := by dsimp [B]; positivity
  have hfloor : 2 ^ (T.S.n k - 1) / B = L := (class_card_exact D j).symm
  have hdiv : 2 ^ (T.S.n k - 1) / B < L + 1 := by omega
  have hlt : 2 ^ (T.S.n k - 1) < (L + 1) * B := (Nat.div_lt_iff_lt_mul hB).mp hdiv
  have hdouble : L + 1 ≤ 2 * L := by omega
  have hmul := Nat.mul_le_mul_right B hdouble
  have hgroup : B ≤ 2 * T.S.n k := (syndrome_group_size D).2.le
  have hmul' := Nat.mul_le_mul_left (2 * L) hgroup
  have hpow : 2 ^ T.S.n k = 2 ^ (T.S.n k - 1) * 2 := by
    have he : T.S.n k = (T.S.n k - 1) + 1 := by omega
    conv_lhs => rw [he]
    rw [pow_succ]
  rw [hpow]
  dsimp [L] at hlt hmul hmul'
  nlinarith

end HypercubeRamsey.S18.Lane_sol_s18_n5
