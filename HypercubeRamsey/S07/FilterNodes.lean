import HypercubeRamsey.S07.GeometryNodes
import HypercubeRamsey.S07.FilterNodes_q_s07_filter

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
  by_cases hn2 : 2 ≤ n
  · have hcross := crossValidRow_retention Γ M (σ c.1) (fun h => W (h, c.2)) c.1
      hn hd hloc hv.1
    have hcross' :
        (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) ≤
          filterMass E G (M.ν (σ c.1)) (crossLabels Γ W c) := by
      simpa [crossLabels, GridGeom.crossNames, Function.comp_def] using hcross
    have hfactor : 0 ≤ 1 - (n : ℝ) ^ (-2 : ℝ) := one_sub_npow_nonneg_q hn2
    calc
      (1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(2 * (d / 80) * (s : ℝ))) ≤
          (1 - (n : ℝ) ^ (-2 : ℝ)) *
            filterMass E G (M.ν (σ c.1)) (crossLabels Γ W c) :=
        mul_le_mul_of_nonneg_left hcross' hfactor
      _ ≤ filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) := hv.2
  · have hnEq : n = 1 := by omega
    subst n
    norm_num
    exact filterMass_nonneg E G (M.ν (σ c.1)) (cellLabels Γ W c)

/-- L7.1b(iii) (07:103–113): on a valid cell, removing one copy of a listed name's label loses at most the
retained fraction `delTheta`: the own list keeps `1 - n^{-2}` after the cross list, and the cross order with the
deleted key last keeps `n^{-c}` at its last step. -/
theorem cellValid_delete_retention (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hn : 1 ≤ n) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N) (c w : Γ.Cell)
    (hv : CellValid Γ M σ W c) (hw : w ∈ Γ.fullNames c) :
    delTheta Γ c w * filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) ≤
      filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) := by
  classical
  by_cases hn2 : 2 ≤ n
  · have hfactor : 0 ≤ 1 - (n : ℝ) ^ (-2 : ℝ) := one_sub_npow_nonneg_q hn2
    by_cases hown : w.1 = c.1
    · have hcrossNot : w ∉ Γ.crossNames c.1 c.2 := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨h, hh, heq⟩
        have hfirst : h = w.1 := congrArg Prod.fst heq
        have hEq : h = c.1 := hfirst.trans hown
        subst h
        have hkey : c.1 ∈ Γ.keyNbrs c.1 := by
          rw [hEq] at hh
          simpa [GridGeom.crossKeys] using hh
        have hdist : Γ.keyDist c.1 c.1 = 1 := (Finset.mem_filter.mp hkey).2
        have hself : Γ.keyDist c.1 c.1 = 0 := by simp [GridGeom.keyDist]
        omega
      have hwown : w ∈ Γ.ownNames c.1 c.2 := by
        have hmem : w ∈ Γ.crossNames c.1 c.2 ∨ w ∈ Γ.ownNames c.1 c.2 := by
          simpa [GridGeom.fullNames] using hw
        exact hmem.resolve_left hcrossNot
      let Lcross := crossLabels Γ W c
      let Lown := (Γ.ownNames c.1 c.2).map W
      have hfull : cellLabels Γ W c = Lcross ++ Lown := by
        simp [Lcross, Lown, cellLabels, GridGeom.fullNames, crossLabels, GridGeom.crossNames]
      have htarget : W w ∈ Lown := by
        exact List.mem_map.mpr ⟨w, hwown, rfl⟩
      have hdel :
          filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) ≤
            filterMass E G (M.ν (σ c.1)) Lcross := by
        rw [hfull]
        apply filterMass_le_of_mem
        intro x hx
        exact mem_append_erase_of_mem_suffix htarget hx
      have htheta : delTheta Γ c w = 1 - (n : ℝ) ^ (-2 : ℝ) := by
        simp [delTheta, hown]
      rw [htheta]
      calc
        (1 - (n : ℝ) ^ (-2 : ℝ)) *
            filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) ≤
          (1 - (n : ℝ) ^ (-2 : ℝ)) * filterMass E G (M.ν (σ c.1)) Lcross :=
          mul_le_mul_of_nonneg_left hdel hfactor
        _ ≤ filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) := by
          simpa [Lcross, OwnValid, hfull] using hv.2
    · have hwcross : w ∈ Γ.crossNames c.1 c.2 := by
        have hmem : w ∈ Γ.crossNames c.1 c.2 ∨ w ∈ Γ.ownNames c.1 c.2 := by
          simpa [GridGeom.fullNames] using hw
        rcases hmem with hmem | hmem
        · exact hmem
        · rcases List.mem_map.mp hmem with ⟨t, ht, heq⟩
          exact False.elim (hown (congrArg Prod.fst heq).symm)
      have hwcross' : w ∈ (Γ.crossKeys c.1).map (fun h => (h, c.2)) := by
        simpa [GridGeom.crossNames] using hwcross
      obtain ⟨h₀, hh₀, heq⟩ := List.mem_map.mp hwcross'
      let a : Γ.Key → Fin N := fun h => W (h, c.2)
      let preKeys := (Γ.crossKeys c.1).erase h₀
      let preLabels := preKeys.map a
      let order := Γ.crossOrder c.1 h₀
      let orderLabels := order.map a
      let ownLabels := (Γ.ownNames c.1 c.2).map W
      have htarget : a h₀ = W w := by
        simpa [a] using congrArg W heq
      have horderLabels : orderLabels = preLabels ++ [a h₀] := by
        simp [orderLabels, order, preLabels, preKeys, GridGeom.crossOrder, List.map_append]
      have hpreStep :
          (n : ℝ) ^ (-(d / 80)) *
              filterMass E G (M.ν (σ c.1)) preLabels ≤
            filterMass E G (M.ν (σ c.1)) orderLabels := by
        have hk : preKeys.length < (Γ.crossKeys c.1).length := by
          have hlen : preKeys.length + 1 = (Γ.crossKeys c.1).length := by
            simpa [preKeys] using List.length_erase_add_one hh₀
          omega
        have hstep := hv.1 h₀ hh₀ preKeys.length hk
        have htake0 : orderLabels.take preKeys.length = preLabels := by
          rw [horderLabels, List.take_append_of_le_length (by simp [preLabels])]
          simp [preLabels]
        have hlen : orderLabels.length = preKeys.length + 1 := by
          simp [horderLabels, preLabels]
        have htake1 : orderLabels.take (preKeys.length + 1) = orderLabels := by
          rw [← hlen]
          exact List.take_length
        have hstep' := hstep
        change (n : ℝ) ^ (-(d / 80)) *
            filterMass E G (M.ν (σ c.1)) (orderLabels.take preKeys.length) ≤
          filterMass E G (M.ν (σ c.1)) (orderLabels.take (preKeys.length + 1)) at hstep'
        rw [htake0, htake1] at hstep'
        exact hstep'
      have hlabelsPerm : List.Perm (orderLabels ++ ownLabels) (cellLabels Γ W c) := by
        have hp := (crossOrder_perm Γ c.1 h₀ hh₀).map a |>.append_right ownLabels
        simpa [orderLabels, ownLabels, cellLabels, GridGeom.fullNames, GridGeom.crossNames,
          GridGeom.ownNames, a, List.map_append, Function.comp_def] using hp
      have hdelEq :
          filterMass E G (M.ν (σ c.1)) ((orderLabels ++ ownLabels).erase (W w)) =
            filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) :=
        filterMass_congr_mem E G (M.ν (σ c.1)) (fun x => (hlabelsPerm.erase (W w)).mem_iff)
      have htargetSuffix : W w ∈ [a h₀] ++ ownLabels := by
        rw [← htarget]
        exact List.mem_append.mpr (Or.inl (by simp))
      have hprefixMem : ∀ x, x ∈ preLabels →
          x ∈ (orderLabels ++ ownLabels).erase (W w) := by
        intro x hx
        have hm := mem_append_erase_of_mem_suffix htargetSuffix hx
        simpa [horderLabels, List.append_assoc] using hm
      have hdel :
          filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) ≤
            filterMass E G (M.ν (σ c.1)) preLabels := by
        rw [← hdelEq]
        apply filterMass_le_of_mem
        exact hprefixMem
      have hcrossEq :
          filterMass E G (M.ν (σ c.1)) orderLabels =
            filterMass E G (M.ν (σ c.1)) (crossLabels Γ W c) := by
        have hp : List.Perm orderLabels (crossLabels Γ W c) := by
          have hp' := (crossOrder_perm Γ c.1 h₀ hh₀).map a
          simpa [orderLabels, crossLabels, GridGeom.crossNames, a, Function.comp_def] using hp'
        exact filterMass_congr_mem E G (M.ν (σ c.1)) (fun x => hp.mem_iff)
      have hpreStep' :
          (n : ℝ) ^ (-(d / 80)) *
              filterMass E G (M.ν (σ c.1)) preLabels ≤
            filterMass E G (M.ν (σ c.1)) (crossLabels Γ W c) := by
        simpa [hcrossEq] using hpreStep
      have hrpos : 0 < (n : ℝ) ^ (-(d / 80)) := by
        have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        exact Real.rpow_pos_of_pos hnreal _
      have hret := hv.2
      rw [delTheta, if_neg hown] at *
      calc
        ((1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(d / 80))) *
            filterMass E G (M.ν (σ c.1)) ((cellLabels Γ W c).erase (W w)) ≤
          ((1 - (n : ℝ) ^ (-2 : ℝ)) * (n : ℝ) ^ (-(d / 80))) *
            filterMass E G (M.ν (σ c.1)) preLabels :=
          mul_le_mul_of_nonneg_left hdel (mul_nonneg hfactor hrpos.le)
        _ ≤ (1 - (n : ℝ) ^ (-2 : ℝ)) *
            filterMass E G (M.ν (σ c.1)) (crossLabels Γ W c) := by
          calc
            _ = (1 - (n : ℝ) ^ (-2 : ℝ)) *
                ((n : ℝ) ^ (-(d / 80)) *
                  filterMass E G (M.ν (σ c.1)) preLabels) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hpreStep' hfactor
        _ ≤ filterMass E G (M.ν (σ c.1)) (cellLabels Γ W c) := hret
  · have hnEq : n = 1 := by omega
    subst n
    simp [delTheta]
    exact filterMass_nonneg E G (M.ν (σ c.1)) (cellLabels Γ W c)

/-- L7.1b(iii) (07:101–102, 114): deletion is by name, so a deletion law does not read the deleted variable: the
erased label list has the label set of the other (distinct) names. -/
theorem delRow_update (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ) :
    DelUpdate Γ M := by
  classical
  intro σ W c w z hw
  let L := Γ.fullNames c
  have hnot : w ∉ L.erase w := (hloc.fullNames_nodup c).not_mem_erase
  have hmap : (L.erase w).map (Function.update W w z) = (L.erase w).map W := by
    apply List.map_congr_left
    intro u hu
    have hun : u ≠ w := by
      intro heq
      subst u
      exact hnot hu
    exact Function.update_of_ne hun _ _
  have hmem : ∀ x,
      x ∈ (L.map (Function.update W w z)).erase z ↔
        x ∈ (L.map W).erase (W w) := by
    intro x
    have hl := mem_map_erase (hloc.fullNames_nodup c) hw (Function.update W w z) x
    have hr := mem_map_erase (hloc.fullNames_nodup c) hw W x
    simpa [Function.update_self, hmap] using hl.trans (by rw [hmap]; exact hr.symm)
  have hmass :
      filterMass E G (M.ν (σ c.1)) ((L.map (Function.update W w z)).erase z) =
        filterMass E G (M.ν (σ c.1)) ((L.map W).erase (W w)) :=
    filterMass_congr_mem E G (M.ν (σ c.1)) hmem
  have hlabelsNew : cellLabels Γ (Function.update W w z) c =
      (L.map (Function.update W w z)) := rfl
  have hlabelsOld : cellLabels Γ W c = (L.map W) := rfl
  unfold delRow
  rw [hlabelsNew, hlabelsOld, Function.update_self]
  have hpass (x : Fin N) :
      passesAnchors E G ((L.map (Function.update W w z)).erase z) x ↔
        passesAnchors E G ((L.map W).erase (W w)) x := by
    unfold passesAnchors
    constructor
    · intro h y hy
      exact h y ((hmem y).mpr hy)
    · intro h y hy
      exact h y ((hmem y).mp hy)
  have hweight (x : Fin N) :
      (filtLaw E G (M.ν (σ c.1)) ((L.map (Function.update W w z)).erase z)).w x =
        (filtLaw E G (M.ν (σ c.1)) ((L.map W).erase (W w))).w x := by
    unfold filtLaw
    by_cases hp : 0 < filterMass E G (M.ν (σ c.1)) ((L.map (Function.update W w z)).erase z)
    · have hp' : 0 < filterMass E G (M.ν (σ c.1)) ((L.map W).erase (W w)) := by
        rw [← hmass]
        exact hp
      simp [hp, hp', filt, hmass, hpass]
    · have hp' : ¬ 0 < filterMass E G (M.ν (σ c.1)) ((L.map W).erase (W w)) := by
        intro hp'
        exact hp (by simpa [hmass] using hp')
      simp [hp, hp', hmass]
  cases hL : filtLaw E G (M.ν (σ c.1)) ((L.map (Function.update W w z)).erase z) with
  | mk wL hnonnegL hsumL =>
    cases hR : filtLaw E G (M.ν (σ c.1)) ((L.map W).erase (W w)) with
    | mk wR hnonnegR hsumR =>
      have hws : wL = wR := by
        funext x
        have hx := hweight x
        simpa [hL, hR] using hx
      subst wR
      rfl

/-- L7.1f(i) (07:207–214): `F_z ≤ exp(c·sℓ·log n + 2/n) Q_v`.  Each neighbouring row is at most `delTheta⁻¹`
times its deletion law for the name of `v`'s cell, which does not read `z`; at most `sℓ` neighbours list that
name as a cross name. -/
theorem starLik_le_starRef (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hn : 2 ≤ n)
    (hd : 0 ≤ d) (hloc : GeomLocal Γ) (hdel : DelCompare Γ M) (hupd : DelUpdate Γ M) :
    StarLikBound Γ M := by
  classical
  intro σ W v z y
  let W' := Function.update W (Γ.key v) z
  let theta (j : Fin n) := delTheta Γ (Γ.key (cubeFlip v j)) (Γ.key v)
  let factorExp (j : Fin n) :=
    (if (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 then 0
      else (d / 80) * Real.log (n : ℝ)) + 2 * (n : ℝ) ^ (-2 : ℝ)
  have hname (j : Fin n) :
      Γ.key v ∈ Γ.fullNames (Γ.key (cubeFlip v j)) :=
    hloc.names_adj (cubeFlip v j) v (cubeFlip_adj v j).symm
  have hrowNonneg (j : Fin n) :
      0 ≤ cellRow Γ M σ W' (Γ.key (cubeFlip v j)) (y j) := by
    unfold cellRow
    split_ifs with hv
    · exact filt_nonneg_q E G (M.ν (σ (Γ.key (cubeFlip v j)).1))
        (cellLabels Γ W' (Γ.key (cubeFlip v j))) (y j)
    · exact le_rfl
  have hfactor (j : Fin n) :
      cellRow Γ M σ W' (Γ.key (cubeFlip v j)) (y j) ≤
        (theta j)⁻¹ * (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j) := by
    by_cases hv : CellValid Γ M σ W' (Γ.key (cubeFlip v j))
    · have hbound := hdel σ W' (Γ.key (cubeFlip v j)) (Γ.key v) hv (hname j) (y j)
      have hupdate := hupd σ W (Γ.key (cubeFlip v j)) (Γ.key v) z (hname j)
      rw [hupdate] at hbound
      exact hbound
    · rw [cellRow, if_neg hv]
      have hthetaPos := delTheta_pos_q Γ hn hd (Γ.key (cubeFlip v j)) (Γ.key v)
      exact mul_nonneg (inv_nonneg.mpr hthetaPos.le)
        ((delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).nonneg (y j))
  have hthetaFactor (j : Fin n) : (theta j)⁻¹ ≤ Real.exp (factorExp j) := by
    simpa [theta, factorExp, eq_comm] using
      delTheta_inv_le_exp Γ hn hd (Γ.key (cubeFlip v j)) (Γ.key v)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hgamma : 0 ≤ d / 80 := div_nonneg hd (by norm_num)
  have hgammaLog : 0 ≤ (d / 80) * Real.log (n : ℝ) := mul_nonneg hgamma hlog
  let cross : Finset (Fin n) := Finset.univ.filter
    (fun j => (Γ.key (cubeFlip v j)).1 ≠ (Γ.key v).1)
  have hcrossCount : (cross.card : ℝ) ≤ (s * ℓ : ℕ) := by
    exact_mod_cast hloc.cross_count v
  have hcrossSum :
      (∑ j : Fin n,
        if (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 then (0 : ℝ)
          else (d / 80) * Real.log (n : ℝ)) =
        (cross.card : ℝ) * ((d / 80) * Real.log (n : ℝ)) := by
    have hpoint (j : Fin n) :
        (if (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 then (0 : ℝ)
          else (d / 80) * Real.log (n : ℝ)) =
          (if j ∈ cross then (1 : ℝ) else 0) * ((d / 80) * Real.log (n : ℝ)) := by
      by_cases hj : (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 <;> simp [cross, hj]
    calc
      (∑ j : Fin n,
        if (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 then (0 : ℝ)
          else (d / 80) * Real.log (n : ℝ)) =
        ∑ j : Fin n, (if j ∈ cross then (1 : ℝ) else 0) *
          ((d / 80) * Real.log (n : ℝ)) := by simp_rw [hpoint]
      _ = (∑ j : Fin n, if j ∈ cross then (1 : ℝ) else 0) *
          ((d / 80) * Real.log (n : ℝ)) := by rw [← Finset.sum_mul]
      _ = (cross.card : ℝ) * ((d / 80) * Real.log (n : ℝ)) := by
        have hind : (∑ j : Fin n, if j ∈ cross then (1 : ℝ) else 0) = cross.card := by
          simp
        rw [hind]
  have herrorSum :
      (∑ _j : Fin n, 2 * (n : ℝ) ^ (-2 : ℝ)) = 2 / (n : ℝ) := by
    have hpow : (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ := by
      rw [Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) (2 : ℝ)]
      norm_num [Real.rpow_natCast]
    calc
      (∑ _j : Fin n, 2 * (n : ℝ) ^ (-2 : ℝ)) =
          (n : ℝ) * (2 * (n : ℝ) ^ (-2 : ℝ)) := by simp
      _ = 2 / (n : ℝ) := by
        rw [hpow]
        field_simp [ne_of_gt hnreal]
  have hsumExp :
      (∑ j : Fin n, factorExp j) ≤
      (d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ) := by
    rw [Finset.sum_add_distrib]
    calc
      (∑ j : Fin n,
        (if (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 then (0 : ℝ)
          else (d / 80) * Real.log (n : ℝ))) +
          ∑ _j : Fin n, 2 * (n : ℝ) ^ (-2 : ℝ) =
          (cross.card : ℝ) * ((d / 80) * Real.log (n : ℝ)) + 2 / (n : ℝ) := by
        rw [hcrossSum, herrorSum]
      _ ≤ ((s * ℓ : ℕ) : ℝ) * ((d / 80) * Real.log (n : ℝ)) + 2 / (n : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right hcrossCount hgammaLog) le_rfl
      _ = (d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ) := by ring
  have hthetaProd :
      (∏ j : Fin n, (theta j)⁻¹) ≤
        Real.exp ((d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ)) := by
    calc
      (∏ j : Fin n, (theta j)⁻¹) ≤ ∏ j : Fin n, Real.exp (factorExp j) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact inv_nonneg.mpr (delTheta_pos_q Γ hn hd (Γ.key (cubeFlip v j)) (Γ.key v)).le
        · intro j hj
          exact hthetaFactor j
      _ = Real.exp (∑ j : Fin n, factorExp j) := by rw [← Real.exp_sum]
      _ ≤ Real.exp ((d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ)) :=
        Real.exp_le_exp.mpr hsumExp
  have hrefNonneg :
      0 ≤ ∏ j : Fin n,
        (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j) :=
    Finset.prod_nonneg fun j _ =>
      (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).nonneg (y j)
  change
    (∏ j : Fin n,
      cellRow Γ M σ (Function.update W (Γ.key v) z) (Γ.key (cubeFlip v j)) (y j)) ≤
    Real.exp ((d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ)) *
      (∏ j : Fin n,
        (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j))
  calc
    (∏ j : Fin n,
        cellRow Γ M σ (Function.update W (Γ.key v) z)
          (Γ.key (cubeFlip v j)) (y j)) ≤
      ∏ j : Fin n,
        (theta j)⁻¹ *
          (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j) := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact hrowNonneg j
        · intro j hj
          exact hfactor j
    _ = (∏ j : Fin n, (theta j)⁻¹) *
        (∏ j : Fin n,
          (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ Real.exp ((d / 80) * ((s * ℓ : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ)) *
        (∏ j : Fin n,
          (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).w (y j)) :=
      mul_le_mul_of_nonneg_right hthetaProd hrefNonneg

/-- L7.1h (07:326–332): on predictive success the posterior even row is a probability law supported on the
common `G`-neighbours of the odd labels: a nonzero `F_x` makes every neighbouring row nonzero at its label with
`x` placed at the role's cell, and that cell is listed by every neighbour. -/
theorem evenRow_law (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hloc : GeomLocal Γ)
    (hrow : RowLaw Γ M) : EvenRowLaw Γ M := by
  classical
  intro σ W f a hsuccess
  let v := a.1
  let y := nbrLabels f a
  have hrowNonneg (z : Fin N) (j : Fin n) :
      0 ≤ cellRow Γ M σ (Function.update W (Γ.key v) z)
        (Γ.key (cubeFlip v j)) (y j) :=
    (hrow σ (Function.update W (Γ.key v) z) (Γ.key (cubeFlip v j))).1 (y j)
  have hlikNonneg (z : Fin N) : 0 ≤ starLik Γ M σ W v z y := by
    unfold starLik
    exact Finset.prod_nonneg fun j _ => by
      simpa [v] using hrowNonneg z j
  have hmargNonneg : 0 ≤ starMarg Γ M σ W v y := by
    unfold starMarg
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg ((M.μ (σ (Γ.key v).1)).nonneg z) (hlikNonneg z)
  have hmargNe : starMarg Γ M σ W v y ≠ 0 := by
    intro hz
    apply hsuccess
    left
    exact hz
  have hmargPos : 0 < starMarg Γ M σ W v y := by
    by_contra hnot
    have hz : starMarg Γ M σ W v y = 0 := by linarith
    exact hmargNe hz
  have hnumSum :
      (∑ z : Fin N,
        starLik Γ M σ W v z y * (M.μ (σ (Γ.key v).1)).w z) =
        starMarg Γ M σ W v y := by
    unfold starMarg
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hrowNonnegX (z : Fin N) : 0 ≤ evenRowAt Γ M σ W a y z := by
    unfold evenRowAt
    exact div_nonneg
      (mul_nonneg (hlikNonneg z) ((M.μ (σ (Γ.key v).1)).nonneg z)) hmargPos.le
  have hrowSum : (∑ z : Fin N, evenRowAt Γ M σ W a y z) = 1 := by
    unfold evenRowAt
    calc
      (∑ z : Fin N,
        starLik Γ M σ W v z y * (M.μ (σ (Γ.key v).1)).w z /
          starMarg Γ M σ W v y) =
          (∑ z : Fin N,
            starLik Γ M σ W v z y * (M.μ (σ (Γ.key v).1)).w z) /
              starMarg Γ M σ W v y := by rw [Finset.sum_div]
      _ = 1 := by rw [hnumSum]; exact div_self (ne_of_gt hmargPos)
  refine ⟨?_, ?_, ?_⟩
  · intro z
    simpa [evenRow, y] using hrowNonnegX z
  · simpa [evenRow, y] using hrowSum
  · intro z hz b hab
    have hadj : (cube n).Adj a.1 b.1 := hab
    have hlikNe : starLik Γ M σ W v z y ≠ 0 := by
      have hEvenAt : evenRowAt Γ M σ W a y z ≠ 0 := by
        simpa [evenRow, y] using hz
      have hnum :
          starLik Γ M σ W v z y * (M.μ (σ (Γ.key v).1)).w z ≠ 0 := by
        intro hzero
        apply hEvenAt
        simp [evenRowAt, v, hzero]
      exact (mul_ne_zero_iff.mp hnum).1
    have hprodNe :
        (∏ j : Fin n,
          cellRow Γ M σ (Function.update W (Γ.key v) z)
            (Γ.key (cubeFlip v j)) (y j)) ≠ 0 := by
      simpa [starLik, v] using hlikNe
    have hrowNe (j : Fin n) :
        cellRow Γ M σ (Function.update W (Γ.key v) z)
          (Γ.key (cubeFlip v j)) (y j) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprodNe) j (Finset.mem_univ j)
    change _root_.hammingDist a.1 b.1 = 1 at hab
    let S : Finset (Fin n) := Finset.univ.filter fun j => a.1 j ≠ b.1 j
    have hS : S.card = 1 := by simpa [S, _root_.hammingDist] using hab
    have hSpos : 0 < S.card := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hSpos
    have hne : a.1 j ≠ b.1 j := (Finset.mem_filter.mp hj).2
    have hflip : b.1 = cubeFlip a.1 j := by
      funext k
      by_cases hkj : k = j
      · subst k
        cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [cubeFlip]
      · have hEq : a.1 k = b.1 k := by
          by_contra hneq
          have hk : k ∈ S := by simp [S, hneq]
          have hjk : j ≠ k := by intro heq; exact hkj heq.symm
          have htwo : 1 < S.card := Finset.one_lt_card.mpr ⟨j, hj, k, hk, hjk⟩
          omega
        simp [cubeFlip, Function.update_of_ne hkj, hEq]
    have hoddNbr : oddNbr a j = b := by
      apply Subtype.ext
      exact hflip.symm
    have hy : y j = f b := by
      dsimp [y, nbrLabels]
      rw [hoddNbr]
    have hname : Γ.key a.1 ∈ Γ.fullNames (Γ.key b.1) :=
      hloc.names_adj b.1 a.1 hadj.symm
    let Wz := Function.update W (Γ.key v) z
    have hlabel : z ∈ cellLabels Γ Wz (Γ.key b.1) := by
      apply List.mem_map.mpr
      refine ⟨Γ.key a.1, hname, ?_⟩
      simp [Wz, v, Function.update_self]
    have hpass := (hrow σ Wz (Γ.key b.1)).2.2.2 (y j) (by
      simpa [Wz, v, hflip] using hrowNe j)
    rw [← hy]
    exact hpass.1 z hlabel

/-- L7.1h (07:333–335): `N p_v^X ≤ e^{.06q}` on predictive success: `F_x / M_v ≤ e^{.04q + o(q)}` and
`N μ ≤ e^{n^{d/2}} = e^{o(q)}`. -/
theorem evenRow_cap (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ),
      0 < N → StarLikBound Γ M → EvenRowCap Γ M := by
  obtain ⟨n₀, hn₀⟩ := evenCapRemainder_bound d hd
  refine ⟨n₀, ?_⟩
  intro n hn N E G X Y p κ Γ M hN hstar
  have hrem := hn₀ n hn
  intro σ W a y hsuccess x
  let v := a.1
  have hrowNonneg (z : Fin N) (j : Fin n) :
      0 ≤ cellRow Γ M σ (Function.update W (Γ.key v) z)
        (Γ.key (cubeFlip v j)) (y j) := by
    unfold cellRow
    split_ifs
    · exact filt_nonneg_q E G (M.ν (σ (Γ.key (cubeFlip v j)).1))
        (cellLabels Γ (Function.update W (Γ.key v) z) (Γ.key (cubeFlip v j))) (y j)
    · exact le_rfl
  have hlikNonneg (z : Fin N) : 0 ≤ starLik Γ M σ W v z y := by
    unfold starLik
    exact Finset.prod_nonneg fun j _ => by
      simpa [v] using hrowNonneg z j
  have hmargNonneg : 0 ≤ starMarg Γ M σ W v y := by
    unfold starMarg
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg ((M.μ (σ (Γ.key v).1)).nonneg z) (hlikNonneg z)
  have hmargNe : starMarg Γ M σ W v y ≠ 0 := by
    intro hz
    apply hsuccess
    left
    exact hz
  have hmargPos : 0 < starMarg Γ M σ W v y := by
    by_contra hnot
    have hz : starMarg Γ M σ W v y = 0 := by linarith
    exact hmargNe hz
  have hrefNonneg : 0 ≤ starRef Γ M σ W v y := by
    unfold starRef
    exact Finset.prod_nonneg fun j _ =>
      (delRow Γ M σ W (Γ.key (cubeFlip v j)) (Γ.key v)).nonneg (y j)
  have hnotPred :
      ¬ (starMarg Γ M σ W v y = 0 ∨
        starMarg Γ M σ W v y < Real.exp (-(4 / 100 : ℝ) * (gQ d n : ℝ)) *
          starRef Γ M σ W v y) := by
    simpa [PredFail] using hsuccess
  have hmargin :
      Real.exp (-(4 / 100 : ℝ) * (gQ d n : ℝ)) * starRef Γ M σ W v y ≤
        starMarg Γ M σ W v y := by
    by_contra h
    exact hnotPred (Or.inr (lt_of_not_ge h))
  by_cases href0 : starRef Γ M σ W v y = 0
  · have hlikUpper : starLik Γ M σ W v x y ≤ 0 := by
      simpa [href0] using hstar σ W v x y
    have hlikEq : starLik Γ M σ W v x y = 0 := le_antisymm hlikUpper (hlikNonneg x)
    have hzero : evenRowAt Γ M σ W a y x = 0 := by
      simp [evenRowAt, hlikEq, v]
    rw [hzero]
    simp only [mul_zero]
    exact Real.exp_nonneg _
  · have hrefPos : 0 < starRef Γ M σ W v y := by
      by_contra h
      have hz : starRef Γ M σ W v y = 0 := by linarith
      exact href0 hz
    let C := (d / 80) * ((gS d n * gL d n : ℕ) : ℝ) * Real.log (n : ℝ) + 2 / (n : ℝ)
    let k := (4 / 100 : ℝ) * (gQ d n : ℝ)
    have hdenPos : 0 < Real.exp (-k) * starRef Γ M σ W v y :=
      mul_pos (Real.exp_pos _) hrefPos
    have hmarginK : Real.exp (-k) * starRef Γ M σ W v y ≤ starMarg Γ M σ W v y := by
      simpa [k] using hmargin
    have hratioBound :
        starLik Γ M σ W v x y / starMarg Γ M σ W v y ≤
          (Real.exp C * starRef Γ M σ W v y) /
            (Real.exp (-k) * starRef Γ M σ W v y) := by
      apply (div_le_div_iff₀ hmargPos hdenPos).2
      calc
        starLik Γ M σ W v x y * (Real.exp (-k) * starRef Γ M σ W v y) ≤
            (Real.exp C * starRef Γ M σ W v y) *
              (Real.exp (-k) * starRef Γ M σ W v y) :=
          mul_le_mul_of_nonneg_right (hstar σ W v x y) hdenPos.le
        _ ≤ (Real.exp C * starRef Γ M σ W v y) * starMarg Γ M σ W v y :=
          mul_le_mul_of_nonneg_left hmarginK (by positivity)
    have hratioEq :
        (Real.exp C * starRef Γ M σ W v y) /
          (Real.exp (-k) * starRef Γ M σ W v y) = Real.exp (C + k) := by
      calc
        (Real.exp C * starRef Γ M σ W v y) /
            (Real.exp (-k) * starRef Γ M σ W v y) =
            Real.exp C / Real.exp (-k) := by
              field_simp [ne_of_gt hrefPos, (Real.exp_pos (-k)).ne']
        _ = Real.exp C * Real.exp k := by
              rw [div_eq_mul_inv, Real.exp_neg]
              simp
        _ = Real.exp (C + k) := by rw [← Real.exp_add]
    have hratio :
        starLik Γ M σ W v x y / starMarg Γ M σ W v y ≤ Real.exp (C + k) :=
      hratioBound.trans_eq hratioEq
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hμcap :
        (N : ℝ) * (M.μ (σ (Γ.key v).1)).w x ≤
          Real.exp ((n : ℝ) ^ (d / 2)) := by
      calc
        (N : ℝ) * (M.μ (σ (Γ.key v).1)).w x ≤
            (N : ℝ) * (Real.exp ((n : ℝ) ^ (d / 2)) / N) :=
          mul_le_mul_of_nonneg_left ((M.pure (σ (Γ.key v).1)).1 x) hNpos.le
        _ = Real.exp ((n : ℝ) ^ (d / 2)) := by field_simp [ne_of_gt hNpos]
    have htop :
        (N : ℝ) * evenRowAt Γ M σ W a y x ≤
          Real.exp ((n : ℝ) ^ (d / 2) + C + k) := by
      calc
        (N : ℝ) * evenRowAt Γ M σ W a y x =
            ((N : ℝ) * (M.μ (σ (Γ.key v).1)).w x) *
              (starLik Γ M σ W v x y / starMarg Γ M σ W v y) := by
                rw [evenRowAt]
                dsimp [v]
                field_simp [ne_of_gt hmargPos]
                <;> ring
        _ ≤ Real.exp ((n : ℝ) ^ (d / 2)) *
              (starLik Γ M σ W v x y / starMarg Γ M σ W v y) :=
          mul_le_mul_of_nonneg_right hμcap
            (div_nonneg (hlikNonneg x) hmargPos.le)
        _ ≤ Real.exp ((n : ℝ) ^ (d / 2)) * Real.exp (C + k) :=
          mul_le_mul_of_nonneg_left hratio (Real.exp_nonneg _)
        _ = Real.exp ((n : ℝ) ^ (d / 2) + C + k) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hexp :
        (n : ℝ) ^ (d / 2) + C + k ≤ (6 / 100 : ℝ) * (gQ d n : ℝ) := by
      dsimp [C, k]
      nlinarith [hrem]
    calc
      (N : ℝ) * evenRowAt Γ M σ W a y x ≤ Real.exp ((n : ℝ) ^ (d / 2) + C + k) := htop
      _ ≤ Real.exp ((6 / 100 : ℝ) * (gQ d n : ℝ)) := Real.exp_le_exp.mpr hexp

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
