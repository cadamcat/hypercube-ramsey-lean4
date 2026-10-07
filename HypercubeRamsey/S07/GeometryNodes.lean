import HypercubeRamsey.S07.Experiment
import HypercubeRamsey.S07.GeometryNodes_q_s07_geom

/-!
# L7.1a: geometry facts

Source: `sections/07-…tex`, lines 55–82, 172, 183, 211–214, 233–237, 253, 273–274, 283, 341–345.  The four nodes
hold for every grid geometry; `geomFacts` bundles them for the later stages.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey

variable {d : ℝ} {n s ℓ q : ℕ}

/-- L7.1a(i)–(ii) (07:61–63, 79–82, 211–214, 235–237): a coordinate flip moves the cell by distance at most one
and the flipped vertex's cell is listed by the original cell (a special flip keeps the key or moves one bin, an
auxiliary flip changes one auxiliary bit, a residual flip changes neither); only the `sℓ` special coordinates
change the grid key; `|E(g)| ≤ 2s`; `q + 1` own words; the listed names are distinct. -/
theorem grid_local (Γ : GridGeom d n s ℓ q) : GeomLocal Γ := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v hadj
    have hadj' : _root_.hammingDist u v = 1 := by
      change _root_.hammingDist u v = 1 at hadj
      exact hadj
    have hhd : (Finset.univ.filter fun j : Fin n => u j ≠ v j).card = 1 := by
      simpa [_root_.hammingDist] using hadj'
    obtain ⟨j, hset⟩ := Finset.card_eq_one.mp hhd
    have hdiff : u j ≠ v j := by
      have hj : j ∈ Finset.univ.filter fun i : Fin n => u i ≠ v i := by
        rw [hset]
        simp
      exact (Finset.mem_filter.mp hj).2
    have hsame (i : Fin n) (hi : i ≠ j) : u i = v i := by
      by_contra hne
      have hiMem : i ∈ Finset.univ.filter fun k : Fin n => u k ≠ v k := by simp [hne]
      rw [hset] at hiMem
      have : i = j := by simpa using hiMem
      exact hi this
    have hflip : v = cubeFlip u j := by
      funext i
      by_cases hi : i = j
      · subst i
        have hbit : v j = !u j := by
          cases hu : u j <;> cases hv : v j <;> simp_all
        simp [cubeFlip, hbit]
      · simp [cubeFlip, Function.update_of_ne hi, hsame i hi]
    let c := Γ.key u
    let c' := Γ.key (cubeFlip u j)
    have hdist : Γ.cellDist c c' ≤ 1 := by
      simpa [c, c'] using GridGeom.cellDist_flip_le_one Γ u j
    have hsum : Γ.keyDist c.1 c'.1 + Γ.auxDist c.2 c'.2 ≤ 1 := by
      simpa [GridGeom.cellDist] using hdist
    by_cases hk : Γ.keyDist c.1 c'.1 = 1
    · have ha : Γ.auxDist c.2 c'.2 = 0 := by omega
      have hteq : c.2 = c'.2 := (GridGeom.auxDist_eq_zero_iff Γ c.2 c'.2).mp ha
      have hkmem : c'.1 ∈ Γ.keyNbrs c.1 := by simpa [GridGeom.keyNbrs] using hk
      have hcrossList : c'.1 ∈ Γ.crossKeys c.1 := by
        simpa [GridGeom.crossKeys] using hkmem
      have hcross : c' ∈ Γ.crossNames c.1 c.2 := by
        unfold GridGeom.crossNames
        apply List.mem_map.mpr
        exact ⟨c'.1, hcrossList, Prod.ext rfl hteq⟩
      rw [hflip]
      simpa [GridGeom.fullNames, c, c'] using
        (List.mem_append.mpr (Or.inl hcross))
    · have hk0 : Γ.keyDist c.1 c'.1 = 0 := by omega
      have hkeq : c.1 = c'.1 := (GridGeom.keyDist_eq_zero_iff Γ c.1 c'.1).mp hk0
      have ha : Γ.auxDist c.2 c'.2 ≤ 1 := by omega
      have hownWord : c'.2 ∈ Γ.ownWords c.2 := by
        unfold GridGeom.ownWords
        exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩)
      have hown : c' ∈ Γ.ownNames c.1 c.2 := by
        unfold GridGeom.ownNames
        apply List.mem_map.mpr
        exact ⟨c'.2, hownWord, Prod.ext hkeq rfl⟩
      rw [hflip]
      simpa [GridGeom.fullNames, c, c'] using
        (List.mem_append.mpr (Or.inr hown))
  · intro v j
    exact GridGeom.cellDist_flip_le_one Γ v j
  · intro v
    let U := Finset.univ.biUnion Γ.chunk
    have hsub :
        (Finset.univ.filter fun j => (Γ.key (cubeFlip v j)).1 ≠ (Γ.key v).1) ⊆ U := by
      intro j hj
      by_contra hmem
      have hnot : ∀ r, j ∉ Γ.chunk r := by
        intro r hr
        apply hmem
        exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, hr⟩
      have heq : (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 := by
        funext r
        exact GridGeom.key_first_flip_eq_of_not_mem_chunk Γ v j r (hnot r)
      exact (Finset.mem_filter.mp hj).2 heq
    have hUcard : U.card ≤ s * ℓ := by
      calc
        (Finset.univ.biUnion Γ.chunk).card ≤ ∑ r ∈ Finset.univ, (Γ.chunk r).card :=
          Finset.card_biUnion_le
        _ = s * ℓ := by simp [Γ.chunk_card]
    exact (Finset.card_le_card hsub).trans hUcard
  · intro g
    exact GridGeom.keyNbrs_card_le Γ g
  · intro t
    exact GridGeom.auxBall_one_card_q_s07_geom Γ t
  · intro c
    have hcross : (Γ.crossNames c.1 c.2).Nodup := by
      unfold GridGeom.crossNames GridGeom.crossKeys
      apply List.Nodup.map
      · intro h h' heq
        exact congrArg Prod.fst heq
      · exact Finset.nodup_toList _
    have hown : (Γ.ownNames c.1 c.2).Nodup := by
      unfold GridGeom.ownNames GridGeom.ownWords
      apply List.Nodup.map
      · intro t t' heq
        exact congrArg Prod.snd heq
      · exact Finset.nodup_toList _
    have hdisjoint : List.Disjoint (Γ.crossNames c.1 c.2) (Γ.ownNames c.1 c.2) := by
      unfold GridGeom.crossNames GridGeom.crossKeys GridGeom.ownNames GridGeom.ownWords
      rw [List.disjoint_left]
      intro x hx hy
      rcases List.mem_map.mp hx with ⟨h, hh, rfl⟩
      rcases List.mem_map.mp hy with ⟨t, ht, hpair⟩
      have hkey : h = c.1 := (congrArg Prod.fst hpair).symm
      subst h
      have hdist : Γ.keyDist c.1 c.1 = 1 := by
        simpa [GridGeom.keyNbrs] using (Finset.mem_toList.mp hh)
      simp [GridGeom.keyDist] at hdist
    exact List.Nodup.append hcross hown hdisjoint

/-- Ball sizes (07:172, 253, 283, 355): radius-`R` balls have at most `(2s+1)^R` keys, `(q+1)^R` auxiliary words
and `(2s+q+1)^R` cells. -/
theorem grid_balls (Γ : GridGeom d n s ℓ q) : GeomBalls Γ := by
  classical
  have hauxball : ∀ t : Γ.AuxWord, (Γ.auxBall t 1).card = q + 1 := by
    intro t
    exact GridGeom.auxBall_one_card_q_s07_geom Γ t
  refine ⟨?_, ?_, ?_⟩
  · intro g R
    have hdegree : ∀ x : Γ.Key,
        (Finset.univ.filter fun y => Γ.keyDist x y = 1).card ≤ 2 * s := by
      intro x
      simpa [GridGeom.keyNbrs] using GridGeom.keyNbrs_card_le Γ x
    have hnat : (Γ.keyBall g R).card ≤ (2 * s + 1) ^ R := by
      unfold GridGeom.keyBall
      exact finiteBall_card_le_of_geodesic Γ.keyDist g R (2 * s)
        (fun x y hz => (GridGeom.keyDist_eq_zero_iff Γ x y).mp hz)
        (fun x y hne => GridGeom.keyDist_geodesic Γ x y hne)
        hdegree
    exact_mod_cast hnat
  · intro t R
    have hdegree : ∀ x : Γ.AuxWord,
        (Finset.univ.filter fun y => Γ.auxDist x y = 1).card ≤ q := by
      intro x
      exact le_of_eq (GridGeom.auxNbrs_card_of_auxBall_one_card Γ x (hauxball x))
    have hnat : (Γ.auxBall t R).card ≤ (q + 1) ^ R := by
      unfold GridGeom.auxBall
      exact finiteBall_card_le_of_geodesic Γ.auxDist t R q
        (fun x y hz => (GridGeom.auxDist_eq_zero_iff Γ x y).mp hz)
        (fun x y hne => GridGeom.auxDist_geodesic Γ x y hne)
        hdegree
    exact_mod_cast hnat
  · intro c R
    have hdegree : ∀ x : Γ.Cell,
        (Finset.univ.filter fun y => Γ.cellDist x y = 1).card ≤ 2 * s + q := by
      intro x
      exact GridGeom.cellNbrs_card_le Γ x hauxball
    have hzero : ∀ x y : Γ.Cell, Γ.cellDist x y = 0 → x = y := by
      intro x y hxy
      have hsum : Γ.keyDist x.1 y.1 + Γ.auxDist x.2 y.2 = 0 := by
        simpa [GridGeom.cellDist] using hxy
      have hk : Γ.keyDist x.1 y.1 = 0 := by omega
      have ha : Γ.auxDist x.2 y.2 = 0 := by omega
      exact Prod.ext ((GridGeom.keyDist_eq_zero_iff Γ x.1 y.1).mp hk)
        ((GridGeom.auxDist_eq_zero_iff Γ x.2 y.2).mp ha)
    have hnat : (Γ.cellBall c R).card ≤ (2 * s + q + 1) ^ R := by
      unfold GridGeom.cellBall
      exact finiteBall_card_le_of_geodesic Γ.cellDist c R (2 * s + q)
        hzero (fun x y hne => GridGeom.cellDist_geodesic Γ x y hne) hdegree
    exact_mod_cast hnat

/-- L7.1a(iii) (07:65–68): with a residual coordinate, each parity class has `2^{n-1}` vertices, and the vertices
of one parity reading the cell `(g, t)` are the fraction `2^{-q} ∏_r Pr[Bin(ℓ,1/2) ∈ bin g_r]` of the class; the
key masses sum to one and are at most `(2n^{-d/4})^s`. -/
theorem grid_counts (Γ : GridGeom d n s ℓ q) : GeomCounts Γ := by
  classical
  obtain ⟨jresidual, _, _⟩ := Γ.residual_nonempty
  have hjresidualLt := jresidual.isLt
  have hn : 0 < n := by omega
  obtain ⟨hEvenSet, hOddSet⟩ := HypercubeRamsey.parity_class_card hn
  have hEvenCardEq : Fintype.card (EvenRole n) = (HypercubeRamsey.evenRoleSet n).card := by
    rw [Fintype.card_subtype]
    simp [HypercubeRamsey.evenRoleSet]
  have hEvenCard : Fintype.card (EvenRole n) = 2 ^ (n - 1) := hEvenCardEq.trans hEvenSet
  have hOddSetEq :
      (Finset.univ.filter fun v : CubeVertex n => ¬ IsEvenRole v) =
        (Finset.univ \ HypercubeRamsey.evenRoleSet n) := by
    ext v
    simp [HypercubeRamsey.evenRoleSet]
  have hOddCardEq : Fintype.card (OddRole n) =
      (Finset.univ \ HypercubeRamsey.evenRoleSet n).card := by
    rw [Fintype.card_subtype]
    exact congrArg Finset.card hOddSetEq
  have hOddCard : Fintype.card (OddRole n) = 2 ^ (n - 1) := hOddCardEq.trans hOddSet
  have hatomSum :
      (∑ k : Fin (ℓ + 1), ((Nat.choose ℓ k.val : ℕ) : ℝ) / (2 : ℝ) ^ ℓ) = 1 := by
    have hchoose :
        (∑ i ∈ Finset.range (ℓ + 1), (Nat.choose ℓ i : ℕ) : ℝ) = (2 : ℝ) ^ ℓ := by
      exact_mod_cast Nat.sum_range_choose ℓ
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((Nat.choose ℓ i : ℕ) : ℝ) / (2 : ℝ) ^ ℓ) (ℓ + 1)]
    rw [← Finset.sum_div, hchoose]
    field_simp
  have hbinMassSum (r : Fin s) : ∑ b : Fin (Γ.bins r), Γ.binMass r b = 1 := by
    simp_rw [GridGeom.binMass]
    rw [Finset.sum_comm]
    simp [hatomSum, eq_comm]
  have hkeyMassSum : ∑ g : Γ.Key, Γ.keyMass g = 1 := by
    unfold GridGeom.keyMass
    rw [← Fintype.prod_sum]
    simp_rw [hbinMassSum]
    simp
  have hkeyMassLe :
      ∀ g : Γ.Key, Γ.keyMass g ≤ (2 * (n : ℝ) ^ (-(d / 4))) ^ s := by
    intro g
    have hnonneg : ∀ r : Fin s, 0 ≤ Γ.binMass r (g r) := by
      intro r
      unfold GridGeom.binMass
      positivity
    calc
      Γ.keyMass g = ∏ r : Fin s, Γ.binMass r (g r) := rfl
      _ ≤ ∏ _ : Fin s, 2 * (n : ℝ) ^ (-(d / 4)) := by
        apply Finset.prod_le_prod₀
        · intro r hr
          exact hnonneg r
        · intro r hr
          exact Γ.bin_mass r (g r)
      _ = (2 * (n : ℝ) ^ (-(d / 4))) ^ s := by simp
  let U : Finset (Fin n) := Finset.univ.biUnion Γ.chunk
  let S : Finset (Fin n) := Γ.aux ∪ U
  have hchunksPairwise :
      ((Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint Γ.chunk := by
    intro r hr r' hr' hne
    exact Γ.chunks_disjoint hne
  have hUCard : U.card = s * ℓ := by
    calc
      U.card = ∑ r ∈ Finset.univ, (Γ.chunk r).card := by
        dsimp [U]
        exact Finset.card_biUnion hchunksPairwise
      _ = s * ℓ := by simp [Γ.chunk_card]
  have hAuxDisjU : Disjoint Γ.aux U := by
    apply Finset.disjoint_left.mpr
    intro j hjA hjU
    rcases Finset.mem_biUnion.mp hjU with ⟨r, _, hjChunk⟩
    exact (Finset.disjoint_left.mp (Γ.aux_disjoint r)) hjA hjChunk
  have hSCard : S.card = q + s * ℓ := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hAuxDisjU, Γ.aux_card, hUCard]
  obtain ⟨jres, hjresAux, hjresChunks⟩ := Γ.residual_nonempty
  have hjresU : jres ∉ U := by
    intro hj
    rcases Finset.mem_biUnion.mp hj with ⟨r, _, hmem⟩
    exact hjresChunks r hmem
  have hjresS : jres ∉ S := by simp [S, hjresAux, hjresU]
  have hSlt : S.card < n := by
    have hne : S ≠ Finset.univ := by
      intro heq
      apply hjresS
      rw [heq]
      exact Finset.mem_univ _
    have hss : S ⊂ (Finset.univ : Finset (Fin n)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩
    simpa using Finset.card_lt_card hss
  have hEvenCount : ∀ c : Γ.Cell,
      ((Finset.univ.filter fun a : EvenRole n => Γ.key a.1 = c).card : ℝ) =
        (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 := by
    intro c
    let chunkPred : ∀ r : Fin s, (Γ.chunk r → Bool) → Prop := fun r f =>
      Γ.bin r (GridGeom.chunkPatternIndex_q_s07_geom Γ r f) = c.1 r
    let chunkWords := ∀ r : Fin s, Γ.chunk r → Bool
    let goodWords := {f : chunkWords // ∀ r, chunkPred r (f r)}
    let goodAux := {t : Γ.AuxWord // t = c.2}
    let goodParts := {p : Γ.AuxWord × chunkWords // p.1 = c.2 ∧ ∀ r, chunkPred r (p.2 r)}
    have hWordsEquiv : goodWords ≃ ∀ r : Fin s, {f : Γ.chunk r → Bool // chunkPred r f} :=
      piSubtypeEquiv_q_s07_geom chunkPred
    have hpatternCard (r : Fin s) :
        Fintype.card {f : Γ.chunk r → Bool // chunkPred r f} =
          ∑ k : Fin (ℓ + 1),
            if Γ.bin r k = c.1 r then Nat.choose ℓ k.val else 0 := by
      simpa [chunkPred, Fintype.card_subtype] using
        (GridGeom.chunkPatternCard_q_s07_geom Γ r (c.1 r))
    have hwordsCard : Fintype.card goodWords =
        ∏ r : Fin s, ∑ k : Fin (ℓ + 1),
          if Γ.bin r k = c.1 r then Nat.choose ℓ k.val else 0 := by
      calc
        Fintype.card goodWords =
            Fintype.card (∀ r : Fin s, {f : Γ.chunk r → Bool // chunkPred r f}) :=
          Fintype.card_congr hWordsEquiv
        _ = ∏ r : Fin s, Fintype.card {f : Γ.chunk r → Bool // chunkPred r f} := by simp
        _ = _ := by simp_rw [hpatternCard]
    have hPartsEquiv : goodParts ≃ goodAux × goodWords := {
      toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2, p.2.2⟩⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl
    }
    have hauxGoodCard : Fintype.card goodAux = 1 := by simp [goodAux]
    have hpartsCard : Fintype.card goodParts = Fintype.card goodWords := by
      calc
        Fintype.card goodParts = Fintype.card goodAux * Fintype.card goodWords := by
          simpa [Fintype.card_prod] using (Fintype.card_congr hPartsEquiv)
        _ = Fintype.card goodWords := by simp [hauxGoodCard]
    let eSplit : (∀ i : S, Bool) ≃ Γ.AuxWord × chunkWords :=
      GridGeom.auxChunkWordsEquiv Γ
    let readPart (p : Γ.AuxWord × chunkWords) : Γ.Cell :=
      ((fun r => Γ.bin r (GridGeom.chunkPatternIndex_q_s07_geom Γ r (p.2 r))), p.1)
    let goodPattern := {z : (∀ i : S, Bool) //
      (eSplit z).1 = c.2 ∧ ∀ r, chunkPred r ((eSplit z).2 r)}
    have hPatternEquiv : goodPattern ≃ goodParts := {
      toFun := fun z => ⟨eSplit z.1, z.2⟩
      invFun := fun p => ⟨eSplit.symm p.1, by simpa using p.2⟩
      left_inv := by intro z; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp
    }
    let goodSet : Finset (∀ i : S, Bool) := Finset.univ.filter fun z =>
      (eSplit z).1 = c.2 ∧ ∀ r, chunkPred r ((eSplit z).2 r)
    have hgoodSetCard : goodSet.card = Fintype.card goodParts := by
      calc
        goodSet.card = Fintype.card goodPattern := by
          simp [goodSet, goodPattern, Fintype.card_subtype]
        _ = Fintype.card goodParts := Fintype.card_congr hPatternEquiv
    have hgoodPatternCard : goodSet.card =
        ∏ r : Fin s, ∑ k : Fin (ℓ + 1),
          if Γ.bin r k = c.1 r then Nat.choose ℓ k.val else 0 := by
      rw [hgoodSetCard, hpartsCard, hwordsCard]
    let restrict (v : CubeVertex n) : ∀ i : S, Bool := fun i => v i.1
    have hchunkRestrict (v : CubeVertex n) (r : Fin s) :
        (eSplit (restrict v)).2 r = fun j => v j.1 := by
      funext j
      change (GridGeom.auxChunkWordsEquiv Γ
        (fun i : ↥(Γ.aux ∪ GridGeom.chunkUnion_q_s07_geom Γ) => v i.1)).2 r j = v j.1
      exact GridGeom.auxChunkWordsEquiv_apply_chunk Γ
        (fun i : ↥(Γ.aux ∪ GridGeom.chunkUnion_q_s07_geom Γ) => v i.1) r j
    have hauxRestrict (v : CubeVertex n) :
        (eSplit (restrict v)).1 = fun j => v j.1 := by
      funext j
      change (GridGeom.auxChunkWordsEquiv Γ
        (fun i : ↥(Γ.aux ∪ GridGeom.chunkUnion_q_s07_geom Γ) => v i.1)).1 j = v j.1
      exact GridGeom.auxChunkWordsEquiv_apply_aux Γ
        (fun i : ↥(Γ.aux ∪ GridGeom.chunkUnion_q_s07_geom Γ) => v i.1) j
    have hreadCell (v : CubeVertex n) : readPart (eSplit (restrict v)) = Γ.key v := by
      dsimp [readPart]
      apply Prod.ext
      · funext r
        change Γ.bin r
          (GridGeom.chunkPatternIndex_q_s07_geom Γ r ((eSplit (restrict v)).2 r)) =
          (Γ.key v).1 r
        rw [hchunkRestrict v r, GridGeom.chunkPatternIndex_restrict_q_s07_geom]
        exact (GridGeom.key_first_apply Γ v r).symm
      · exact (hauxRestrict v).trans (GridGeom.key_second_apply Γ v).symm
    let restrRole (a : EvenRole n) : ∀ i : S, Bool := restrict a.1
    let evenCellSet := Finset.univ.filter fun a : EvenRole n => Γ.key a.1 = c
    have hmaps : (evenCellSet : Set (EvenRole n)).MapsTo restrRole (goodSet : Set (∀ i : S, Bool)) := by
      intro a ha
      have hkey : Γ.key a.1 = c := (Finset.mem_filter.mp ha).2
      have hcell : readPart (eSplit (restrRole a)) = c := (hreadCell a.1).trans hkey
      have hgood : (eSplit (restrRole a)).1 = c.2 ∧
          ∀ r, chunkPred r ((eSplit (restrRole a)).2 r) := by
        constructor
        · exact congrArg Prod.snd hcell
        · intro r
          exact congrFun (congrArg Prod.fst hcell) r
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩
    have hcardFibers :=
      finset_card_fibers_real_q_s07_geom evenCellSet goodSet restrRole hmaps
    have hgood (z : ∀ i : S, Bool) (hz : z ∈ goodSet) : readPart (eSplit z) = c := by
      have hp := (Finset.mem_filter.mp hz).2
      apply Prod.ext
      · funext r
        exact hp.2 r
      · exact hp.1
    have hfiber (z : ∀ i : S, Bool) (hz : z ∈ goodSet) :
        (evenCellSet.filter fun a => restrRole a = z).card =
          (Finset.univ.filter fun a : EvenRole n => restrRole a = z).card := by
      apply congrArg Finset.card
      ext a
      simp only [evenCellSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hrestr⟩
        exact hrestr
      · intro hrestr
        refine ⟨?_, hrestr⟩
        have hsplit : eSplit (restrRole a) = eSplit z := congrArg eSplit hrestr
        calc
          Γ.key a.1 = readPart (eSplit (restrRole a)) := (hreadCell a.1).symm
          _ = readPart (eSplit z) := congrArg readPart hsplit
          _ = c := hgood z hz
    have hparityFiber (z : ∀ i : S, Bool) :
        (Finset.univ.filter fun a : EvenRole n => restrRole a = z).card =
          2 ^ (n - S.card - 1) := by
      let roleZ := {a : EvenRole n // restrRole a = z}
      let cubeZ := {v : CubeVertex n // IsEvenRole v ∧ ∀ i : S, v i.1 = z i}
      have hEquiv : roleZ ≃ cubeZ := {
        toFun := fun a => (⟨a.1.1, ⟨a.1.2, by
          intro i
          simpa [restrRole, restrict] using congrFun a.2 i⟩⟩ : cubeZ)
        invFun := fun v => (⟨⟨v.1, v.2.1⟩, by
          funext i
          simpa [restrRole, restrict] using v.2.2 i⟩ : roleZ)
        left_inv := by
          intro a
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro v
          apply Subtype.ext
          rfl
      }
      have hleft : Fintype.card roleZ =
          (Finset.univ.filter fun a : EvenRole n => restrRole a = z).card := by
        simp [roleZ, Fintype.card_subtype]
      have hright : Fintype.card cubeZ =
          ((HypercubeRamsey.evenRoleSet n).filter fun v => ∀ i : S, v i.1 = z i).card := by
        simp [cubeZ, HypercubeRamsey.evenRoleSet, Fintype.card_subtype,
          Finset.filter_filter, and_assoc, and_left_comm, and_comm]
      calc
        (Finset.univ.filter fun a : EvenRole n => restrRole a = z).card = Fintype.card roleZ :=
          hleft.symm
        _ = Fintype.card cubeZ := Fintype.card_congr hEquiv
        _ = ((HypercubeRamsey.evenRoleSet n).filter fun v => ∀ i : S, v i.1 = z i).card :=
          hright
        _ = 2 ^ (n - S.card - 1) :=
          HypercubeRamsey.parity_projection_uniform S hSlt z
    have hEvenTotal : evenCellSet.card = goodSet.card * 2 ^ (n - S.card - 1) := by
      calc
        evenCellSet.card =
            ∑ z ∈ goodSet, (evenCellSet.filter fun a => restrRole a = z).card := by
          exact Finset.card_eq_sum_card_fiberwise hmaps
        _ = ∑ z ∈ goodSet, 2 ^ (n - S.card - 1) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [hfiber z hz, hparityFiber z]
        _ = goodSet.card * 2 ^ (n - S.card - 1) := by simp
    let C : Fin s → ℕ := fun r =>
      ∑ k : Fin (ℓ + 1), if Γ.bin r k = c.1 r then Nat.choose ℓ k.val else 0
    have hchunkMass (r : Fin s) :
        (C r : ℝ) = (2 : ℝ) ^ ℓ * Γ.binMass r (c.1 r) := by
      have hcast : (C r : ℝ) =
          ∑ k : Fin (ℓ + 1),
            if Γ.bin r k = c.1 r then (Nat.choose ℓ k.val : ℝ) else 0 := by
        dsimp [C]
        norm_cast
      rw [hcast, GridGeom.binMass]
      calc
        (∑ k : Fin (ℓ + 1),
            if Γ.bin r k = c.1 r then (Nat.choose ℓ k.val : ℝ) else 0) =
            ∑ k : Fin (ℓ + 1), (2 : ℝ) ^ ℓ *
              (if Γ.bin r k = c.1 r then
                (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hbin : Γ.bin r k = c.1 r
          · simp [hbin]
            field_simp
          · simp [hbin]
        _ = (2 : ℝ) ^ ℓ *
            ∑ k : Fin (ℓ + 1),
              if Γ.bin r k = c.1 r then
                (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ else 0 := by
          rw [Finset.mul_sum]
        _ = (2 : ℝ) ^ ℓ * Γ.binMass r (c.1 r) := rfl
    have hgoodReal :
        (goodSet.card : ℝ) = (2 : ℝ) ^ (s * ℓ) * Γ.keyMass c.1 := by
      have hCcard : goodSet.card = ∏ r : Fin s, C r := by
        rw [hgoodPatternCard]
      calc
        (goodSet.card : ℝ) = ∏ r : Fin s, (C r : ℝ) := by exact_mod_cast hCcard
        _ = ∏ r : Fin s, ((2 : ℝ) ^ ℓ * Γ.binMass r (c.1 r)) := by
          apply Finset.prod_congr rfl
          intro r hr
          exact hchunkMass r
        _ = (∏ _ : Fin s, (2 : ℝ) ^ ℓ) *
              (∏ r : Fin s, Γ.binMass r (c.1 r)) := by
          rw [Finset.prod_mul_distrib]
        _ = (2 : ℝ) ^ (s * ℓ) * Γ.keyMass c.1 := by
          rw [GridGeom.keyMass]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul]
          have hpow : (2 : ℝ) ^ (ℓ * s) = (2 : ℝ) ^ (s * ℓ) :=
            congrArg (fun m : ℕ => (2 : ℝ) ^ m) (Nat.mul_comm ℓ s)
          exact congrArg
            (fun x : ℝ => x * (∏ r : Fin s, Γ.binMass r (c.1 r))) hpow
    have hEvenTotalR : (evenCellSet.card : ℝ) =
        (goodSet.card : ℝ) * (2 : ℝ) ^ (n - S.card - 1) := by
      exact_mod_cast hEvenTotal
    have hused : q + s * ℓ < n := by simpa [hSCard] using hSlt
    have hpowScalar : (2 : ℝ) ^ (s * ℓ) * (2 : ℝ) ^ (n - S.card - 1) =
        (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ q)⁻¹ := by
      have hexp : s * ℓ + (n - S.card - 1) + q = n - 1 := by
        rw [hSCard]
        omega
      have hpoweq : (2 : ℝ) ^ (s * ℓ) * (2 : ℝ) ^ (n - S.card - 1) * (2 : ℝ) ^ q =
          (2 : ℝ) ^ (n - 1) := by
        calc
          (2 : ℝ) ^ (s * ℓ) * (2 : ℝ) ^ (n - S.card - 1) * (2 : ℝ) ^ q =
              (2 : ℝ) ^ (s * ℓ + (n - S.card - 1) + q) := by
            rw [← pow_add, ← pow_add]
          _ = (2 : ℝ) ^ (n - 1) := by rw [hexp]
      have hq : (2 : ℝ) ^ q ≠ 0 := by positivity
      calc
        (2 : ℝ) ^ (s * ℓ) * (2 : ℝ) ^ (n - S.card - 1) =
            ((2 : ℝ) ^ (s * ℓ) * (2 : ℝ) ^ (n - S.card - 1) * (2 : ℝ) ^ q) *
              ((2 : ℝ) ^ q)⁻¹ := by field_simp [hq]
        _ = (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ q)⁻¹ := by rw [hpoweq]
    have hEvenCardR : (Fintype.card (EvenRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
      exact_mod_cast hEvenCard
    change (evenCellSet.card : ℝ) =
      (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1
    calc
      (evenCellSet.card : ℝ) =
          (goodSet.card : ℝ) * (2 : ℝ) ^ (n - S.card - 1) := hEvenTotalR
      _ = (2 : ℝ) ^ (s * ℓ) * Γ.keyMass c.1 * (2 : ℝ) ^ (n - S.card - 1) := by
        rw [hgoodReal]
      _ = (2 : ℝ) ^ (s * ℓ) * (2 : ℝ) ^ (n - S.card - 1) * Γ.keyMass c.1 := by ring
      _ = (2 : ℝ) ^ (n - 1) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 := by rw [hpowScalar]
      _ = (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 := by rw [hEvenCardR]
  have hOddCount : ∀ c : Γ.Cell,
      ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) =
        (Fintype.card (OddRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 := by
    intro c
    obtain ⟨j, hjAux, hjChunks⟩ := Γ.residual_nonempty
    have hkeyflip (v : CubeVertex n) : Γ.key (cubeFlip v j) = Γ.key v := by
      have hfirst : (Γ.key (cubeFlip v j)).1 = (Γ.key v).1 := by
        funext r
        exact GridGeom.key_first_flip_eq_of_not_mem_chunk Γ v j r (hjChunks r)
      have haux : Γ.auxDist (Γ.key v).2 (Γ.key (cubeFlip v j)).2 = 0 := by
        rw [GridGeom.key_auxDist_flip]
        simp [hjAux]
      have hsecond : (Γ.key (cubeFlip v j)).2 = (Γ.key v).2 :=
        ((GridGeom.auxDist_eq_zero_iff Γ (Γ.key v).2 (Γ.key (cubeFlip v j)).2).mp haux).symm
      exact Prod.ext hfirst hsecond
    let evenCell : Type := {a : EvenRole n // Γ.key a.1 = c}
    let oddCell : Type := {u : OddRole n // Γ.key u.1 = c}
    have hEquiv : evenCell ≃ oddCell := {
      toFun := fun a =>
        ⟨⟨cubeFlip a.1.1 j, by
            intro h
            exact ((cubeFlip_parity a.1.1 j).mp h) a.1.2⟩,
          by simpa [hkeyflip] using a.2⟩
      invFun := fun u =>
        ⟨⟨cubeFlip u.1.1 j, (cubeFlip_parity u.1.1 j).mpr u.1.2⟩,
          by simpa [hkeyflip] using u.2⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply Subtype.ext
        funext i
        simp [cubeFlip]
      right_inv := by
        intro u
        apply Subtype.ext
        apply Subtype.ext
        funext i
        simp [cubeFlip]
    }
    have htypeCard : Fintype.card evenCell = Fintype.card oddCell := Fintype.card_congr hEquiv
    have hEvenFilter : Fintype.card evenCell =
        (Finset.univ.filter fun a : EvenRole n => Γ.key a.1 = c).card := by
      simp [evenCell, Fintype.card_subtype]
    have hOddFilter : Fintype.card oddCell =
        (Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card := by
      simp [oddCell, Fintype.card_subtype]
    have hfilterCard :
        (Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card =
      (Finset.univ.filter fun a : EvenRole n => Γ.key a.1 = c).card := by
      calc
        _ = Fintype.card oddCell := hOddFilter.symm
        _ = Fintype.card evenCell := htypeCard.symm
        _ = _ := hEvenFilter
    have hfilterReal :
        ((Finset.univ.filter fun u : OddRole n => Γ.key u.1 = c).card : ℝ) =
          ((Finset.univ.filter fun a : EvenRole n => Γ.key a.1 = c).card : ℝ) := by
      exact_mod_cast hfilterCard
    have hroleCard : Fintype.card (OddRole n) = Fintype.card (EvenRole n) :=
      hOddCard.trans hEvenCard.symm
    rw [hfilterReal]
    simpa [hroleCard] using hEvenCount c
  exact ⟨hEvenCard, hOddCard, hEvenCount, hOddCount, hkeyMassSum, hkeyMassLe⟩

/-- L7.1a(iv) (07:183, 273–274, 341–345): near fractions for the three moment estimates, from the exact counts
and the ball sizes. -/
theorem grid_near (Γ : GridGeom d n s ℓ q) (hB : GeomBalls Γ) (hC : GeomCounts Γ) : GeomNear Γ := by
  classical
  have hauxCard : Fintype.card Γ.AuxWord = 2 ^ q := by
    simp [GridGeom.AuxWord, Fintype.card_fun, Γ.aux_card]
  have hauxDistComm (x y : Γ.AuxWord) : Γ.auxDist x y = Γ.auxDist y x := by
    unfold GridGeom.auxDist
    congr 1
    ext j
    simp [ne_comm]
  have hkeyDistComm (g h : Γ.Key) : Γ.keyDist g h = Γ.keyDist h g := by
    unfold GridGeom.keyDist
    apply Finset.sum_congr rfl
    intro r hr
    exact Nat.dist_comm _ _
  refine ⟨?_, ?_, ?_⟩
  intro a
  let g : Γ.Key := (Γ.key a.1).1
  let S : Finset (EvenRole n) := Finset.univ.filter fun a' => (Γ.key a'.1).1 = g
  let T : Finset Γ.Cell := Finset.univ.filter fun c => c.1 = g
  have hmaps : (S : Set (EvenRole n)).MapsTo (fun a' => Γ.key a'.1) (T : Set Γ.Cell) := by
    intro a' ha'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha').2⟩
  have hcard := finset_card_fibers_real_q_s07_geom S T
    (fun a' : EvenRole n => Γ.key a'.1) hmaps
  have hfiber (c : Γ.Cell) (hc : c ∈ T) :
      (S.filter fun a' => Γ.key a'.1 = c).card =
        (Finset.univ.filter fun a' : EvenRole n => Γ.key a'.1 = c).card := by
    apply congrArg Finset.card
    ext a'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, hkey⟩
      exact hkey
    · intro hkey
      constructor
      · have hc' : c.1 = g := (Finset.mem_filter.mp hc).2
        have hfirst : (Γ.key a'.1).1 = g := (congrArg Prod.fst hkey).trans hc'
        simpa [S] using hfirst
      · exact hkey
  have hcount :
      (S.card : ℝ) =
        ∑ c ∈ T, ((Finset.univ.filter fun a' : EvenRole n => Γ.key a'.1 = c).card : ℝ) := by
    calc
      (S.card : ℝ) =
          ∑ c ∈ T, ((S.filter fun a' => Γ.key a'.1 = c).card : ℝ) := hcard
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        exact_mod_cast hfiber c hc
  have hT : T = ({g} : Finset Γ.Key) ×ˢ (Finset.univ : Finset Γ.AuxWord) := by
    ext c
    rcases c with ⟨g', t'⟩
    simp [T, g, eq_comm]
  have hTcard : T.card = 2 ^ q := by
    rw [hT, Finset.card_product]
    simp [hauxCard]
  have hTcardR : (T.card : ℝ) = (2 : ℝ) ^ q := by exact_mod_cast hTcard
  have hmassKey : ∀ c ∈ T, c.1 = g := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hsumEval :
      ∑ c ∈ T,
        (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 =
        (Fintype.card (EvenRole n) : ℝ) * Γ.keyMass g := by
    calc
      _ = ∑ c ∈ T,
          (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass g := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [hmassKey c hc]
      _ = (T.card : ℝ) *
          ((Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass g) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (Fintype.card (EvenRole n) : ℝ) * Γ.keyMass g := by
        rw [hTcardR]
        have hp : (2 : ℝ) ^ q ≠ 0 := by positivity
        field_simp [hp]
  have hcount' : (S.card : ℝ) =
      (Fintype.card (EvenRole n) : ℝ) * Γ.keyMass g := by
    calc
      (S.card : ℝ) =
          ∑ c ∈ T, ((Finset.univ.filter fun a' : EvenRole n => Γ.key a'.1 = c).card : ℝ) :=
        hcount
      _ = ∑ c ∈ T,
          (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hC.even_count c
      _ = (Fintype.card (EvenRole n) : ℝ) * Γ.keyMass g := hsumEval
  change (S.card : ℝ) ≤
    (2 * (n : ℝ) ^ (-(d / 4))) ^ s * Fintype.card (EvenRole n)
  calc
    (S.card : ℝ) =
        (Fintype.card (EvenRole n) : ℝ) * Γ.keyMass g := hcount'
    _ ≤ ((2 * (n : ℝ) ^ (-(d / 4))) ^ s) * Fintype.card (EvenRole n) := by
      have hcardNonneg : 0 ≤ (Fintype.card (EvenRole n) : ℝ) := by positivity
      calc
        (Fintype.card (EvenRole n) : ℝ) * Γ.keyMass g ≤
            (Fintype.card (EvenRole n) : ℝ) * (2 * (n : ℝ) ^ (-(d / 4))) ^ s :=
          mul_le_mul_of_nonneg_left (hC.keyMass_le g) hcardNonneg
        _ = (2 * (n : ℝ) ^ (-(d / 4))) ^ s * Fintype.card (EvenRole n) := by ring
  · intro u
    let g : Γ.Key := (Γ.key u.1).1
    let K : Finset Γ.Key := Finset.univ.filter fun h => Γ.keyDist h g ≤ 2
    let T : Finset Γ.Cell := K ×ˢ (Finset.univ : Finset Γ.AuxWord)
    let S : Finset (OddRole n) := Finset.univ.filter fun u' =>
      Γ.keyDist (Γ.key u'.1).1 g ≤ 2
    have hK : K = Γ.keyBall g 2 := by
      ext h
      simp [K, GridGeom.keyBall, hkeyDistComm]
    have hmaps : (S : Set (OddRole n)).MapsTo (fun u' => Γ.key u'.1) (T : Set Γ.Cell) := by
      intro u' hu'
      have hdist : Γ.keyDist (Γ.key u'.1).1 g ≤ 2 := (Finset.mem_filter.mp hu').2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist⟩, Finset.mem_univ _⟩
    have hcard := finset_card_fibers_real_q_s07_geom S T
      (fun u' : OddRole n => Γ.key u'.1) hmaps
    have hfiber (c : Γ.Cell) (hc : c ∈ T) :
        (S.filter fun u' => Γ.key u'.1 = c).card =
          (Finset.univ.filter fun u' : OddRole n => Γ.key u'.1 = c).card := by
      apply congrArg Finset.card
      ext u'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hkey⟩
        exact hkey
      · intro hkey
        constructor
        ·
          have hcK : c.1 ∈ K := (Finset.mem_product.mp hc).1
          have hcD : Γ.keyDist c.1 g ≤ 2 := (Finset.mem_filter.mp hcK).2
          have hdist' : Γ.keyDist (Γ.key u'.1).1 g ≤ 2 := by
            rw [(congrArg Prod.fst hkey)]
            exact hcD
          simpa [S] using hdist'
        · exact hkey
    have hcount :
        (S.card : ℝ) =
          ∑ c ∈ T, ((Finset.univ.filter fun u' : OddRole n => Γ.key u'.1 = c).card : ℝ) := by
      calc
        (S.card : ℝ) =
            ∑ c ∈ T, ((S.filter fun u' => Γ.key u'.1 = c).card : ℝ) := hcard
        _ = _ := by
          apply Finset.sum_congr rfl
          intro c hc
          exact_mod_cast hfiber c hc
    have hTcard : T.card = K.card * 2 ^ q := by
      simp [T, Finset.card_product, hauxCard]
    have hTcardR : (T.card : ℝ) = (K.card : ℝ) * (2 : ℝ) ^ q := by
      exact_mod_cast hTcard
    let M : ℝ := (2 * (n : ℝ) ^ (-(d / 4))) ^ s
    let scale : ℝ := (Fintype.card (OddRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹
    have hpoint (c : Γ.Cell) (hc : c ∈ T) :
        ((Finset.univ.filter fun u' : OddRole n => Γ.key u'.1 = c).card : ℝ) ≤ scale * M := by
      rw [hC.odd_count c]
      dsimp [scale, M]
      exact mul_le_mul_of_nonneg_left (hC.keyMass_le c.1) (by positivity)
    have hsumBound :
        (∑ c ∈ T,
          ((Finset.univ.filter fun u' : OddRole n => Γ.key u'.1 = c).card : ℝ)) ≤
          (T.card : ℝ) * (scale * M) := by
      calc
        _ ≤ ∑ c ∈ T, scale * M := by
          apply Finset.sum_le_sum
          intro c hc
          exact hpoint c hc
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hpow : (2 : ℝ) ^ q ≠ 0 := by positivity
    have hmain :
        (S.card : ℝ) ≤ (2 * (n : ℝ) ^ (-(d / 4))) ^ s *
          (2 * s + 1 : ℝ) ^ 2 * Fintype.card (OddRole n) := by
      change (S.card : ℝ) ≤ _
      calc
        (S.card : ℝ) =
            ∑ c ∈ T,
              ((Finset.univ.filter fun u' : OddRole n => Γ.key u'.1 = c).card : ℝ) := hcount
        _ ≤ (T.card : ℝ) * (scale * M) := hsumBound
        _ = (K.card : ℝ) * (Fintype.card (OddRole n) : ℝ) * M := by
          dsimp [scale, M]
          rw [hTcardR]
          field_simp [hpow]
        _ ≤ (2 * s + 1 : ℝ) ^ 2 * Fintype.card (OddRole n) *
              (2 * (n : ℝ) ^ (-(d / 4))) ^ s := by
          dsimp [M]
          have hKball : (K.card : ℝ) ≤ (2 * s + 1 : ℝ) ^ 2 := by
            rw [hK]
            exact hB.keyBall_card g 2
          have hodd : 0 ≤ (Fintype.card (OddRole n) : ℝ) := by positivity
          have hbase : 0 ≤ (2 * (n : ℝ) ^ (-(d / 4))) ^ s := by positivity
          have hmid := mul_le_mul_of_nonneg_right hKball hodd
          calc
            (K.card : ℝ) * Fintype.card (OddRole n) *
                (2 * (n : ℝ) ^ (-(d / 4))) ^ s ≤
              ((2 * s + 1 : ℝ) ^ 2 * Fintype.card (OddRole n)) *
                (2 * (n : ℝ) ^ (-(d / 4))) ^ s :=
              mul_le_mul_of_nonneg_right hmid hbase
            _ = (2 * s + 1 : ℝ) ^ 2 * Fintype.card (OddRole n) *
                (2 * (n : ℝ) ^ (-(d / 4))) ^ s := by ring
        _ = (2 * (n : ℝ) ^ (-(d / 4))) ^ s *
              (2 * s + 1 : ℝ) ^ 2 * Fintype.card (OddRole n) := by ring
    have hcomm :
        (2 * (n : ℝ) ^ (-(d / 4))) ^ s * (2 * s + 1 : ℝ) ^ 2 *
            Fintype.card (OddRole n) =
          (2 * s + 1 : ℝ) ^ 2 * (2 * (n : ℝ) ^ (-(d / 4))) ^ s *
            Fintype.card (OddRole n) := by ring
    simpa [S] using hmain.trans_eq hcomm
  · intro a
    let t : Γ.AuxWord := (Γ.key a.1).2
    let A : Finset Γ.AuxWord := Γ.auxBall t 5
    let T : Finset Γ.Cell := (Finset.univ : Finset Γ.Key) ×ˢ A
    let S : Finset (EvenRole n) := Finset.univ.filter fun a' =>
      Γ.auxDist (Γ.key a'.1).2 t ≤ 5
    have hmaps : (S : Set (EvenRole n)).MapsTo (fun a' => Γ.key a'.1) (T : Set Γ.Cell) := by
      intro a' ha'
      have hdist : Γ.auxDist (Γ.key a'.1).2 t ≤ 5 := (Finset.mem_filter.mp ha').2
      have hdist' : Γ.auxDist t (Γ.key a'.1).2 ≤ 5 := by
        simpa [hauxDistComm] using hdist
      exact Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdist'⟩⟩
    have hcard := finset_card_fibers_real_q_s07_geom S T
      (fun a' : EvenRole n => Γ.key a'.1) hmaps
    have hfiber (c : Γ.Cell) (hc : c ∈ T) :
        (S.filter fun a' => Γ.key a'.1 = c).card =
          (Finset.univ.filter fun a' : EvenRole n => Γ.key a'.1 = c).card := by
      apply congrArg Finset.card
      ext a'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, hkey⟩
        exact hkey
      · intro hkey
        constructor
        ·
          have hcA : c.2 ∈ A := (Finset.mem_product.mp hc).2
          have hcD : Γ.auxDist t c.2 ≤ 5 := (Finset.mem_filter.mp hcA).2
          have hcD' : Γ.auxDist c.2 t ≤ 5 := by
            simpa [hauxDistComm] using hcD
          have hdist' : Γ.auxDist (Γ.key a'.1).2 t ≤ 5 := by
            rw [(congrArg Prod.snd hkey)]
            exact hcD'
          simpa [S] using hdist'
        · exact hkey
    have hcount :
        (S.card : ℝ) =
          ∑ c ∈ T, ((Finset.univ.filter fun a' : EvenRole n => Γ.key a'.1 = c).card : ℝ) := by
      calc
        (S.card : ℝ) =
            ∑ c ∈ T, ((S.filter fun a' => Γ.key a'.1 = c).card : ℝ) := hcard
        _ = _ := by
          apply Finset.sum_congr rfl
          intro c hc
          exact_mod_cast hfiber c hc
    have hinner (z : Γ.AuxWord) :
        ∑ g : Γ.Key,
          (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass g =
          (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
      calc
        _ = ((Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹) *
            (∑ g : Γ.Key, Γ.keyMass g) := by
          rw [← Finset.mul_sum]
        _ = (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
          rw [hC.keyMass_sum]
          ring
    have hsumEval :
        ∑ c ∈ T,
          (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 =
          (A.card : ℝ) * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
      calc
        _ = ∑ z ∈ A, ∑ g : Γ.Key,
              (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass g := by
          dsimp only [T]
          rw [Finset.sum_product_right]
        _ = ∑ z ∈ A,
              (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hinner z
        _ = (A.card : ℝ) *
              ((Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ = (A.card : ℝ) * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by ring
    have hcount' :
        (S.card : ℝ) =
          (A.card : ℝ) * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
      calc
        (S.card : ℝ) =
            ∑ c ∈ T, ((Finset.univ.filter fun a' : EvenRole n => Γ.key a'.1 = c).card : ℝ) :=
          hcount
        _ = ∑ c ∈ T,
            (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ * Γ.keyMass c.1 := by
          apply Finset.sum_congr rfl
          intro c hc
          exact hC.even_count c
        _ = (A.card : ℝ) * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := hsumEval
    change (S.card : ℝ) ≤
      (q + 1 : ℝ) ^ 5 * ((2 : ℝ) ^ q)⁻¹ * Fintype.card (EvenRole n)
    calc
      (S.card : ℝ) =
          (A.card : ℝ) * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := hcount'
      _ ≤ (q + 1 : ℝ) ^ 5 * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by
        have hball := hB.auxBall_card t 5
        have hscale : 0 ≤ (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by positivity
        calc
          (A.card : ℝ) * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ =
              (A.card : ℝ) * ((Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹) := by ring
          _ ≤ (q + 1 : ℝ) ^ 5 * ((Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹) :=
            mul_le_mul_of_nonneg_right hball hscale
          _ = (q + 1 : ℝ) ^ 5 * (Fintype.card (EvenRole n) : ℝ) * ((2 : ℝ) ^ q)⁻¹ := by ring
      _ = (q + 1 : ℝ) ^ 5 * ((2 : ℝ) ^ q)⁻¹ * Fintype.card (EvenRole n) := by ring
/-- L7.1a: all geometry facts. -/
theorem geomFacts (Γ : GridGeom d n s ℓ q) : GeomFacts Γ :=
  ⟨grid_local Γ, grid_balls Γ, grid_counts Γ, grid_near Γ (grid_balls Γ) (grid_counts Γ)⟩

end HypercubeRamsey.S07
