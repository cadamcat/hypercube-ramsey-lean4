import HypercubeRamsey.S18.Pullback_sol_s18_n5

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

private theorem adjacent_flip (v u : Pos T k)
    (h : (OAI.HypercubeRamsey.cube (T.S.n k)).Adj v u) :
    ∃ a, u = flipPos v a := by
  have hone : (Finset.univ.filter fun a : Fin (T.S.n k) => v a ≠ u a).card = 1 := h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  refine ⟨a, ?_⟩
  funext t
  by_cases ht : t = a
  · subst t
    have hm : a ∈ Finset.univ.filter fun t : Fin (T.S.n k) => v t ≠ u t := by
      rw [ha]; exact Finset.mem_singleton_self _
    have hne := (Finset.mem_filter.mp hm).2
    simp only [flipPos, Function.update_self]
    cases hv : v a <;> cases hu : u a <;> simp_all
  · have hn : t ∉ Finset.univ.filter fun t : Fin (T.S.n k) => v t ≠ u t := by
      rw [ha]; simpa using ht
    have he : v t = u t := by
      by_contra he
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    simp only [flipPos, Function.update_of_ne ht]
    exact he.symm

noncomputable def twoStep (b : Pos T k) : Finset (Pos T k) :=
  Finset.univ.image fun a : Fin (T.S.n k) × Fin (T.S.n k) => flipPos (flipPos b a.1) a.2

theorem twoStep_card (b : Pos T k) : (twoStep b).card ≤ T.S.n k ^ 2 := by
  simpa only [twoStep, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two] using
    (Finset.card_image_le (s := Finset.univ)
      (f := fun a : Fin (T.S.n k) × Fin (T.S.n k) => flipPos (flipPos b a.1) a.2))

theorem pastPositions_subset_twoStep (D : LateData hPT) (j : Fin D.geom.r)
    (rows : Finset (Pos T k)) : pastPositions D j rows ⊆ rows.biUnion twoStep := by
  intro u hu
  obtain ⟨b, hb, hu⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨a, hadj⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨a', he⟩ := adjacent_flip (flipPos b a) v.1 hadj
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_image.mpr
    ⟨(a, a'), Finset.mem_univ _, he.symm⟩⟩

theorem pastPositions_card (D : LateData hPT) (j : Fin D.geom.r)
    (rows : Finset (Pos T k)) : (pastPositions D j rows).card ≤ rows.card * T.S.n k ^ 2 := by
  calc
    _ ≤ (rows.biUnion twoStep).card := Finset.card_le_card (pastPositions_subset_twoStep D j rows)
    _ ≤ rows.card * T.S.n k ^ 2 :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => twoStep_card b)

theorem rowCells_card (D : LateData hPT) (rows : Finset (Pos T k)) :
    (rowCells D rows).card ≤ rows.card * (T.S.n k * (T.S.n k + 1)) :=
  Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => rowInitialCells_card D b)

noncomputable def ancestors (rows : Finset (Pos T k)) : ℕ → Finset (Pos T k)
  | 0 => rows
  | m + 1 => ancestors rows m ∪ (ancestors rows m).biUnion twoStep

theorem ancestors_card (rows : Finset (Pos T k)) (m : ℕ) :
    (ancestors rows m).card ≤ rows.card * (1 + T.S.n k ^ 2) ^ m := by
  induction m with
  | zero => simp [ancestors]
  | succ m ih =>
    have hstep : (ancestors rows (m + 1)).card ≤ (ancestors rows m).card * (1 + T.S.n k ^ 2) := by
      calc
        _ ≤ (ancestors rows m).card + ((ancestors rows m).biUnion twoStep).card :=
          Finset.card_union_le _ _
        _ ≤ (ancestors rows m).card + (ancestors rows m).card * T.S.n k ^ 2 :=
          Nat.add_le_add_left (Finset.card_biUnion_le_card_mul _ _ _
            (fun b _ => twoStep_card b)) _
        _ = _ := by ring
    calc
      _ ≤ (rows.card * (1 + T.S.n k ^ 2) ^ m) * (1 + T.S.n k ^ 2) :=
        hstep.trans (Nat.mul_le_mul_right _ ih)
      _ = _ := by rw [pow_succ]; ring

theorem ancestors_query_card (D : LateData hPT) (rows : Finset (Pos T k))
    (hrows : rows.card ≤ T.S.n k) (hn : 2 ≤ T.S.n k) (m : ℕ) :
    (rowCells D (ancestors rows m)).card ≤ T.S.n k ^ (3 * m + 4) := by
  have hbase : 1 + T.S.n k ^ 2 ≤ T.S.n k ^ 3 := by
    nlinarith [sq_nonneg (T.S.n k : ℤ)]
  have hplus : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  calc
    _ ≤ (ancestors rows m).card * (T.S.n k * (T.S.n k + 1)) := rowCells_card D _
    _ ≤ (rows.card * (1 + T.S.n k ^ 2) ^ m) * (T.S.n k * (T.S.n k + 1)) :=
      Nat.mul_le_mul_right _ (ancestors_card rows m)
    _ ≤ (T.S.n k * (T.S.n k ^ 3) ^ m) * (T.S.n k * T.S.n k ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hrows (Nat.pow_le_pow_left hbase _))
        (Nat.mul_le_mul_left _ hplus)
    _ = _ := by rw [← pow_mul, pow_add]; ring

theorem ancestors_rows_card (rows : Finset (Pos T k))
    (hrows : rows.card ≤ T.S.n k) (hn : 2 ≤ T.S.n k) (m : ℕ) :
    (ancestors rows m).card ≤ T.S.n k ^ (3 * m + 4) := by
  have hbase : 1 + T.S.n k ^ 2 ≤ T.S.n k ^ 3 := by
    nlinarith [sq_nonneg (T.S.n k : ℤ)]
  have hpow : T.S.n k ≤ T.S.n k ^ 4 :=
    Nat.le_self_pow (by omega) _
  calc
    _ ≤ rows.card * (1 + T.S.n k ^ 2) ^ m := ancestors_card rows m
    _ ≤ T.S.n k ^ 4 * (T.S.n k ^ 3) ^ m :=
      Nat.mul_le_mul (hrows.trans hpow) (Nat.pow_le_pow_left hbase _)
    _ = _ := by rw [← pow_mul, pow_add]; ring

end HypercubeRamsey.S18.Lane_sol_s18_n5
