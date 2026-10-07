import HypercubeRamsey.S07.GeometryNodes

/-!
# L7.1b, L7.1f(i), L7.1h: deterministic filter facts

Source: `sections/07-…tex`, lines 84–114, 207–214, 326–336.  The retention nodes feed the proved cell-filter
lemmas of `CellFilters.lean` (`filt_probability_and_support`, `filt_delete_bound`,
`cell_row_cap_of_retention`) through the assemblies `rowLaw`, `rowCap`, `delCompare`; `filterFacts` bundles all
filter facts.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open scoped BigOperators

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

/-- L7.1b (07:84–96): on a valid cell the listed anchors retain mass at least `(1 - n^{-2}) n^{-2cs}`,
`c = d/80`: each of the at most `2s` cross steps keeps a fraction `n^{-c}`, the own list `1 - n^{-2}`. -/
theorem cellValid_retention (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hloc : GeomLocal Γ) (hn : 1 ≤ n) (hd : 0 ≤ d) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N)
    (c : Γ.Cell) (hv : CellValid Γ M σ W c) :
    (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) ≤
      filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) := by
  sorry

/-- L7.1b(iii) (07:103–113): on a valid cell, removing one copy of a listed name's label loses at most the
retained fraction `delTheta`: the own list keeps `1 - n^{-2}` after the cross list, and the cross order with the
deleted key last keeps `n^{-c}` at its last step. -/
theorem cellValid_delete_retention (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hn : 1 ≤ n) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c w : Γ.Cell)
    (hv : CellValid Γ M σ W c) (hw : w ∈ Γ.fullNames c) :
    delTheta Γ c w * filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) ≤
      filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) := by
  sorry

/-- L7.1b(iii) (07:101–102, 114): deletion is by name, so a deletion law does not read the deleted variable: the
erased label list has the label set of the other (distinct) names. -/
theorem delRow_update (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ) :
    DelUpdate Γ M := by
  sorry

/-- L7.1f(i) (07:207–214): `F_z ≤ exp(c·sℓ·log n + 2/n) Q_v`.  Each neighbouring row is at most `delTheta⁻¹`
times its deletion law for the name of `v`'s cell, which does not read `z`; at most `sℓ` neighbours list that
name as a cross name. -/
theorem starLik_le_starRef (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hn : 2 ≤ n)
    (hd : 0 ≤ d) (hloc : GeomLocal Γ) (hdel : DelCompare Γ M) (hupd : DelUpdate Γ M) :
    StarLikBound Γ M := by
  sorry

/-- L7.1h (07:326–332): on predictive success the posterior even row is a probability law supported on the
common `G`-neighbours of the odd labels: a nonzero `F_x` makes every neighbouring row nonzero at its label with
`x` placed at the role's cell, and that cell is listed by every neighbour. -/
theorem evenRow_law (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ)
    (hrow : RowLaw Γ M) : EvenRowLaw Γ M := by
  sorry

/-- L7.1h (07:333–335): `N p_v^X ≤ e^{.06q}` on predictive success: `F_x / M_v ≤ e^{.04q + o(q)}` and
`N μ ≤ e^{n^{d/2}} = e^{o(q)}`. -/
theorem evenRow_cap (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ),
      0 < N → StarLikBound Γ M → EvenRowCap Γ M := by
  sorry

end Nodes

/-! ## Assemblies -/

section Assemblies

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

private theorem one_sub_npow_pos {n : ℕ} (hn : 2 ≤ n) : 0 < 1 - (n : ℝ) ^ (-2 : ℝ) := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have : (n : ℝ) ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg h1 (by norm_num)
  linarith

private theorem retention_pos {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    0 < (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ t :=
  mul_pos (one_sub_npow_pos hn) (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _)

private theorem filterMass_le_erase (E : Fin N → Fin N → Prop) (G : Colour) (ν : Law N)
    (L : List (Fin N)) (x : Fin N) : filterMass E G ν L ≤ filterMass E G ν (L.erase x) := by
  unfold filterMass
  apply Finset.sum_le_sum
  intro y _
  by_cases hL : passesAnchors E G L y
  · have hL' : passesAnchors E G (L.erase x) y := fun z hz => hL z (List.mem_of_mem_erase hz)
    simp [hL, hL']
  · by_cases hL' : passesAnchors E G (L.erase x) y
    · simp [hL, hL', ν.nonneg y]
    · simp [hL, hL']

private theorem filt_ne_zero_w {E : Fin N → Fin N → Prop} {G : Colour} {ν : Law N}
    {L : List (Fin N)} {y : Fin N} (h : filt E G ν L y ≠ 0) : ν.w y ≠ 0 := by
  intro hy
  apply h
  unfold filt
  split_ifs <;> simp [hy]

/-- L7.1b(i): cell rows are subprobabilities on hits of their lists, probabilities on valid cells. -/
theorem rowLaw (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ)
    (hn : 2 ≤ n) (hd : 0 ≤ d) : RowLaw Γ M := by
  intro σ W c
  by_cases hv : CellValid Γ M σ W c
  · have hmass : 0 < filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) :=
      lt_of_lt_of_le (retention_pos hn _)
        (cellValid_retention Γ M hloc (by omega) hd σ W c hv)
    obtain ⟨h0, h1, hsupp⟩ := filt_probability_and_support E G (M.ν (σ c.1)) (cellLabels Γ W c) hmass
    have hrow : ∀ y, cellRow Γ M σ W c y = filt E G (M.ν (σ c.1)) (cellLabels Γ W c) y := by
      intro y
      simp only [cellRow, if_pos hv]
    refine ⟨fun y => by rw [hrow]; exact h0 y, ?_, fun _ => ?_, fun y hy => ?_⟩
    · simp_rw [hrow]
      exact h1.le
    · simp_rw [hrow]
      exact h1
    · rw [hrow] at hy
      exact ⟨hsupp y hy, filt_ne_zero_w hy⟩
  · have hrow : ∀ y, cellRow Γ M σ W c y = 0 := by
      intro y
      simp only [cellRow, if_neg hv]
    refine ⟨fun y => le_of_eq (hrow y).symm, ?_, fun h => absurd h hv, fun y hy => absurd (hrow y) hy⟩
    simp_rw [hrow]
    simp

/-- L7.1b(ii): `N p_{g,t} ≤ L` (07:94–95), from the retention node and `cell_row_cap_of_retention`. -/
theorem rowCap (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ)
    (hn : 2 ≤ n) (hN : 0 < N) (hd : 0 ≤ d) : RowCap Γ M := by
  intro σ W c y
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hv : CellValid Γ M σ W c
  · have hraw : ∀ y, (M.ν (σ c.1)).w y ≤ Real.exp ((n : ℝ) ^ (d / 2)) / N :=
      (M.pure (σ c.1)).2.1
    have hcap := cell_row_cap_of_retention E G (M.ν (σ c.1)) (cellLabels Γ W c) n s d (d / 80)
      hn hN hraw (cellValid_retention Γ M hloc (by omega) hd σ W c hv) y
    simp only [cellRow, if_pos hv]
    calc (N : ℝ) * filt E G (M.ν (σ c.1)) (cellLabels Γ W c) y
        ≤ (N : ℝ) * (Real.exp ((n : ℝ) ^ (d / 2) + 2 * (d / 80) * (s : ℝ) * Real.log (n : ℝ) + 1) /
            N) := mul_le_mul_of_nonneg_left hcap hNpos.le
      _ = cellCap d n s := by
        unfold cellCap
        exact mul_div_cancel₀ _ hNpos.ne'
  · simp only [cellRow, if_neg hv, mul_zero]
    exact (Real.exp_pos _).le

/-- L7.1b(iii): deletion comparisons on validity (07:103–113), from the deletion-retention node and
`filt_delete_bound`. -/
theorem delCompare (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ)
    (hn : 2 ≤ n) (hd : 0 ≤ d) : DelCompare Γ M := by
  intro σ W c w hv hw y
  have hFull : 0 < filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) :=
    lt_of_lt_of_le (retention_pos hn _) (cellValid_retention Γ M hloc (by omega) hd σ W c hv)
  have hDel : 0 < filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) :=
    lt_of_lt_of_le hFull (filterMass_le_erase E G (M.ν (σ c.1)) (cellLabels Γ W c) (W w))
  have hθ : 0 < delTheta Γ c w := by
    unfold delTheta
    split_ifs
    · exact one_sub_npow_pos hn
    · exact retention_pos hn _
  have hwL : W w ∈ cellLabels Γ W c := List.mem_map_of_mem hw
  have hbound := filt_delete_bound E G (M.ν (σ c.1)) (cellLabels Γ W c) (W w) (delTheta Γ c w) hθ
    hwL hDel hFull (cellValid_delete_retention Γ M (by omega) σ W c w hv hw) y
  have hdelw : (delRow Γ M σ W c w).w y =
      filt E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) y := by
    unfold delRow filtLaw
    rw [dif_pos hDel]
  simp only [cellRow, if_pos hv]
  rw [hdelw]
  exact hbound

/-- All deterministic filter facts, for large `n`. -/
theorem filterFacts (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ),
      0 < N → GeomFacts Γ → FilterFacts Γ M := by
  obtain ⟨n₁, hcap⟩ := evenRow_cap d hd hd'
  refine ⟨max n₁ 2, ?_⟩
  intro n hn N E G X Y p κ Γ M hN hG
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hloc := hG.loc
  have hrow := rowLaw Γ M hloc hn2 hd.le
  have hdel := delCompare Γ M hloc hn2 hd.le
  have hupd := delRow_update Γ M hloc
  have hstar := starLik_le_starRef Γ M hn2 hd.le hloc hdel hupd
  refine
    { row_law := hrow
      row_cap := rowCap Γ M hloc hn2 hN hd.le
      del_compare := hdel
      del_update := hupd
      starRef_update := ?_
      starLik_bound := hstar
      evenRow_law := evenRow_law Γ M hloc hrow
      evenRow_cap := hcap n hn1 Γ M hN hstar }
  intro σ W v z
  funext y
  unfold starRef
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [hupd σ W (Γ.key (cubeFlip v j)) (Γ.key v) z
    (hloc.names_adj (cubeFlip v j) v (cubeFlip_adj v j).symm)]

end Assemblies

end HypercubeRamsey.S07
