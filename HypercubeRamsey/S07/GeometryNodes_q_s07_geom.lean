import HypercubeRamsey.S07.GridGeometry

/-!
Lane-local metric-ball bounds used by the S07 geometry proofs.
-/

namespace HypercubeRamsey.S07

open OAI.HypercubeRamsey

/-- In a finite graph metric, a ball grows by at most the maximum number of neighbors plus one. -/
theorem finiteBall_card_le_of_geodesic
    {V : Type*} [Fintype V] [DecidableEq V]
    (dist : V → V → ℕ) (center : V) (R degree : ℕ)
    (hzero : ∀ x y, dist x y = 0 → x = y)
    (hstep : ∀ x y, 0 < dist x y →
      ∃ z, dist x z + 1 = dist x y ∧ dist z y = 1)
    (hdegree : ∀ x, (Finset.univ.filter fun y => dist x y = 1).card ≤ degree) :
    (Finset.univ.filter fun y => dist center y ≤ R).card ≤ (degree + 1) ^ R := by
  classical
  let ball : ℕ → Finset V := fun r => Finset.univ.filter fun y => dist center y ≤ r
  let nbr : V → Finset V := fun x => Finset.univ.filter fun y => dist x y = 1
  induction R with
  | zero =>
      have hsub : ball 0 ⊆ {center} := by
        intro y hy
        have hy0 : dist center y = 0 := by
          have := (Finset.mem_filter.mp hy).2
          omega
        simpa [hzero center y hy0]
      calc
        (ball 0).card ≤ ({center} : Finset V).card := Finset.card_le_card hsub
        _ = (degree + 1) ^ 0 := by simp
  | succ R ih =>
      have hsub : ball (R + 1) ⊆ ball R ∪ (ball R).biUnion nbr := by
        intro y hy
        have hy' := (Finset.mem_filter.mp hy).2
        by_cases hle : dist center y ≤ R
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩))
        · have hpos : 0 < dist center y := by omega
          obtain ⟨z, hcz, hzy⟩ := hstep center y hpos
          have hz : dist center z ≤ R := by omega
          exact Finset.mem_union.mpr (Or.inr <| Finset.mem_biUnion.mpr
            ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy⟩⟩)
      have hsum : (∑ x ∈ ball R, (nbr x).card) ≤ (ball R).card * degree := by
        calc
          (∑ x ∈ ball R, (nbr x).card) ≤ ∑ x ∈ ball R, degree := by
            apply Finset.sum_le_sum
            intro x hx
            exact hdegree x
          _ = (ball R).card * degree := by simp [Finset.sum_const, nsmul_eq_mul]
      calc
        (ball (R + 1)).card ≤ (ball R ∪ (ball R).biUnion nbr).card := Finset.card_le_card hsub
        _ ≤ (ball R).card + ((ball R).biUnion nbr).card := Finset.card_union_le _ _
        _ ≤ (ball R).card + ∑ x ∈ ball R, (nbr x).card :=
          Nat.add_le_add_left Finset.card_biUnion_le _
        _ ≤ (ball R).card + (ball R).card * degree := Nat.add_le_add_left hsum _
        _ = (degree + 1) * (ball R).card := by ring
        _ ≤ (degree + 1) * ((degree + 1) ^ R) := Nat.mul_le_mul_left _ ih
        _ = (degree + 1) ^ (R + 1) := by rw [pow_succ]; ac_rfl

/-- Cast the finite fiber decomposition formula to real cardinalities. -/
theorem finset_card_fibers_real_q_s07_geom
    {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (f : ι → κ)
    (hmap : (s : Set ι).MapsTo f (t : Set κ)) :
    (s.card : ℝ) = ∑ b ∈ t, ((s.filter fun a => f a = b).card : ℝ) := by
  classical
  exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap

/-- A dependent function satisfying coordinatewise predicates is a function of subtype values. -/
noncomputable def piSubtypeEquiv_q_s07_geom
    {ι : Type*} {β : ι → Type*} (p : ∀ i, β i → Prop) :
    {f : ∀ i, β i // ∀ i, p i (f i)} ≃ ∀ i, {x : β i // p i x} where
  toFun f i := ⟨f.1 i, f.2 i⟩
  invFun f := ⟨fun i => (f i).1, fun i => (f i).2⟩
  left_inv := by
    intro f
    apply Subtype.ext
    rfl
  right_inv := by
    intro f
    funext i
    apply Subtype.ext
    rfl

namespace GridGeom

variable {d : ℝ} {n s ℓ q : ℕ} (Γ : GridGeom d n s ℓ q)

private def chunkOnes (r : Fin s) (v : CubeVertex n) : Finset (Fin n) :=
  (Γ.chunk r).filter fun j => v j = true

private def chunkCount (r : Fin s) (v : CubeVertex n) : ℕ :=
  (chunkOnes Γ r v).card

private def chunkIndex (r : Fin s) (v : CubeVertex n) : Fin (ℓ + 1) :=
  ⟨chunkCount Γ r v, Nat.lt_succ_of_le (by
    calc
      chunkCount Γ r v ≤ (Γ.chunk r).card := Finset.card_filter_le _ _
      _ = ℓ := Γ.chunk_card r)⟩

def chunkPatternIndex_q_s07_geom (r : Fin s) (f : Γ.chunk r → Bool) : Fin (ℓ + 1) :=
  ⟨(Finset.univ.filter fun j : Γ.chunk r => f j = true).card, Nat.lt_succ_of_le (by
    calc
      (Finset.univ.filter fun j : Γ.chunk r => f j = true).card ≤
      (Finset.univ : Finset (Γ.chunk r)).card := Finset.card_filter_le _ _
      _ = ℓ := by simp [Γ.chunk_card r])⟩

/-- Restricting a cube vertex to a chunk gives the same count index as the chunk projection. -/
theorem chunkPatternIndex_restrict_q_s07_geom (r : Fin s) (v : CubeVertex n) :
    chunkPatternIndex_q_s07_geom Γ r (fun j => v j.1) = chunkIndex Γ r v := by
  apply Fin.ext
  have hfilter :
      (Finset.univ.filter fun j : Γ.chunk r => v j.1 = true).card =
        ((Γ.chunk r).filter (fun j => v j = true)).card := by
    rw [Finset.univ_eq_attach]
    rw [Finset.filter_attach (fun j : Fin n => v j = true) (Γ.chunk r)]
    simp
  simpa [chunkPatternIndex_q_s07_geom, chunkIndex, chunkCount, chunkOnes] using hfilter

private noncomputable def boolFinsetEquiv (α : Type*) [Fintype α] [DecidableEq α] :
    (α → Bool) ≃ Finset α where
  toFun f := Finset.univ.filter fun a => f a = true
  invFun A := fun a => decide (a ∈ A)
  left_inv := by
    intro f
    funext a
    cases hfa : f a <;> simp [hfa]
  right_inv := by
    intro A
    ext a
    simp

def chunkUnion_q_s07_geom : Finset (Fin n) := Finset.univ.biUnion Γ.chunk

/-- Boolean assignments on the disjoint union of the chunks are chunkwise assignments. -/
noncomputable def chunkWordsEquiv :
    (chunkUnion_q_s07_geom Γ → Bool) ≃ ∀ r : Fin s, Γ.chunk r → Bool where
  toFun f r j := f ⟨j.1, Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, j.2⟩⟩
  invFun F z :=
    let witnesses := Finset.mem_biUnion.mp z.2
    let r := Classical.choose witnesses
    F r ⟨z.1, (Classical.choose_spec witnesses).2⟩
  left_inv := by
    intro f
    funext z
    dsimp
  right_inv := by
    intro F
    funext r j
    dsimp
    let witnesses := Finset.mem_biUnion.mp
      (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, j.2⟩)
    have hchunk : j.1 ∈ Γ.chunk (Classical.choose witnesses) :=
      (Classical.choose_spec witnesses).2
    have hr : Classical.choose witnesses = r := by
      by_contra hne
      exact (Finset.disjoint_left.mp (Γ.chunks_disjoint hne)) hchunk j.2
    let x : Σ r : Fin s, Γ.chunk r :=
      ⟨Classical.choose witnesses, ⟨j.1, (Classical.choose_spec witnesses).2⟩⟩
    have hxy : x = ⟨r, j⟩ := by
      apply Sigma.subtype_ext
      · exact hr
      · rfl
    change F x.1 x.2 = F r j
    exact congrArg (fun z : Σ r : Fin s, Γ.chunk r => F z.1 z.2) hxy

/-- Assignments on auxiliary coordinates and chunks are exactly assignments on their union. -/
noncomputable def auxChunkWordsEquiv :
    (∀ i : ↥(Γ.aux ∪ chunkUnion_q_s07_geom Γ), Bool) ≃
      Γ.AuxWord × (∀ r : Fin s, Γ.chunk r → Bool) := by
  classical
  have hdisj : Disjoint Γ.aux (chunkUnion_q_s07_geom Γ) := by
    apply Finset.disjoint_left.mpr
    intro j hjAux hjUnion
    rcases Finset.mem_biUnion.mp hjUnion with ⟨r, _, hjChunk⟩
    exact (Finset.disjoint_left.mp (Γ.aux_disjoint r)) hjAux hjChunk
  exact (Equiv.piFinsetUnion (fun _ : Fin n => Bool) hdisj).symm.trans
    (Equiv.prodCongr (Equiv.refl _) (Γ.chunkWordsEquiv))

@[simp] theorem auxChunkWordsEquiv_apply_aux
    (f : ∀ i : ↥(Γ.aux ∪ chunkUnion_q_s07_geom Γ), Bool) (j : Γ.aux) :
    (Γ.auxChunkWordsEquiv f).1 j = f ⟨j.1, Finset.mem_union.mpr (Or.inl j.2)⟩ := by
  classical
  simp [auxChunkWordsEquiv, Equiv.piFinsetUnion]

@[simp] theorem auxChunkWordsEquiv_apply_chunk
    (f : ∀ i : ↥(Γ.aux ∪ chunkUnion_q_s07_geom Γ), Bool)
    (r : Fin s) (j : Γ.chunk r) :
    (Γ.auxChunkWordsEquiv f).2 r j =
      f ⟨j.1, Finset.mem_union.mpr
        (Or.inr (Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ _, j.2⟩))⟩ := by
  classical
  simp [auxChunkWordsEquiv, chunkWordsEquiv, Equiv.piFinsetUnion]

/-- The first projection of the grid key is the bin of the chunk count. -/
theorem key_first_apply (v : CubeVertex n) (r : Fin s) :
    (Γ.key v).1 r = Γ.bin r (chunkIndex Γ r v) := by
  classical
  simp [GridGeom.key, chunkIndex, chunkCount, chunkOnes]

/-- The second projection of the grid key is restriction to auxiliary coordinates. -/
theorem key_second_apply (v : CubeVertex n) : (Γ.key v).2 = fun j : Γ.aux => v j.1 := by
  classical
  simp [GridGeom.key]

/-- A monotone surjective bin map cannot jump over a bin between adjacent counts. -/
theorem bin_adj_bound (r : Fin s) (k k' : Fin (ℓ + 1))
    (hstep : k.val + 1 = k'.val) :
    (Γ.bin r k').val ≤ (Γ.bin r k).val + 1 := by
  have hmono := Γ.bin_monotone r k k' (by omega)
  by_contra hnot
  have hgap : (Γ.bin r k).val + 1 < (Γ.bin r k').val := by omega
  let mid : Fin (Γ.bins r) := ⟨(Γ.bin r k).val + 1, by omega⟩
  obtain ⟨i, hi⟩ := Γ.bin_surjective r mid
  by_cases hki : k.val < i.val
  · have hk'i : k'.val ≤ i.val := by omega
    have hmono' := Γ.bin_monotone r k' i (by omega)
    rw [hi] at hmono'
    have hle : (Γ.bin r k').val ≤ (Γ.bin r k).val + 1 := by simpa [mid] using hmono'
    omega
  · have hik : i.val ≤ k.val := by omega
    have hmono' := Γ.bin_monotone r i k (by omega)
    rw [hi] at hmono'
    have hle : (Γ.bin r k).val + 1 ≤ (Γ.bin r k).val := by simpa [mid] using hmono'
    omega

/-- Binning preserves the fact that two chunk counts differ by at most one. -/
theorem bin_dist_le_one_of_count_dist (r : Fin s) (k k' : Fin (ℓ + 1))
    (h : Nat.dist k.val k'.val ≤ 1) :
    Nat.dist (Γ.bin r k).val (Γ.bin r k').val ≤ 1 := by
  by_cases hle : k.val ≤ k'.val
  · have hsub : k'.val - k.val ≤ 1 := by
      rw [Nat.dist_eq_sub_of_le hle] at h
      exact h
    by_cases heq : k.val = k'.val
    · have hEq : k = k' := Fin.ext heq
      subst k'
      simp
    · have hstep : k.val + 1 = k'.val := by omega
      have hmono := Γ.bin_monotone r k k' (by omega)
      have hbound := Γ.bin_adj_bound r k k' hstep
      rw [Nat.dist_eq_sub_of_le hmono]
      omega
  · have hle' : k'.val ≤ k.val := by omega
    have hsub : k.val - k'.val ≤ 1 := by
      rw [Nat.dist_eq_sub_of_le_right hle'] at h
      exact h
    have hstep : k'.val + 1 = k.val := by omega
    have hmono := Γ.bin_monotone r k' k (by omega)
    have hbound := Γ.bin_adj_bound r k' k hstep
    rw [Nat.dist_eq_sub_of_le_right hmono]
    omega

/-- Flipping a coordinate changes the count in a chunk by one exactly when that coordinate is in it. -/
theorem chunkCount_flip_dist (r : Fin s) (v : CubeVertex n) (j : Fin n) :
    Nat.dist (chunkCount Γ r v) (chunkCount Γ r (cubeFlip v j)) =
      if j ∈ Γ.chunk r then 1 else 0 := by
  classical
  by_cases hj : j ∈ Γ.chunk r
  · by_cases hv : v j = true
    · have hset : chunkOnes Γ r (cubeFlip v j) = (chunkOnes Γ r v).erase j := by
        ext i
        by_cases hij : i = j
        · subst i
          simp [chunkOnes, cubeFlip, hj, hv]
        · have hflip : cubeFlip v j i = v i := by
            change Function.update v j (!v j) i = v i
            exact Function.update_of_ne hij _ _
          simp [chunkOnes, hflip, hij]
      have hjmem : j ∈ chunkOnes Γ r v := by simp [chunkOnes, hj, hv]
      have hcard : chunkCount Γ r v = chunkCount Γ r (cubeFlip v j) + 1 := by
        dsimp [chunkCount]
        rw [hset]
        exact (Finset.card_erase_add_one hjmem).symm
      rw [Nat.dist_eq_sub_of_le_right (by omega), if_pos hj]
      omega
    · have hv' : v j = false := Bool.eq_false_iff.mpr hv
      have hjnot : j ∉ chunkOnes Γ r v := by simp [chunkOnes, hj, hv']
      have hset : chunkOnes Γ r (cubeFlip v j) = insert j (chunkOnes Γ r v) := by
        ext i
        by_cases hij : i = j
        · subst i
          simp [chunkOnes, cubeFlip, hj, hv']
        · have hflip : cubeFlip v j i = v i := by
            change Function.update v j (!v j) i = v i
            exact Function.update_of_ne hij _ _
          simp [chunkOnes, hflip, hij]
      have hcard : chunkCount Γ r (cubeFlip v j) = chunkCount Γ r v + 1 := by
        dsimp [chunkCount]
        rw [hset]
        exact Finset.card_insert_of_notMem hjnot
      rw [Nat.dist_eq_sub_of_le (by omega), if_pos hj]
      omega
  · have hset : chunkOnes Γ r (cubeFlip v j) = chunkOnes Γ r v := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [chunkOnes, hj]
      · have hflip : cubeFlip v j i = v i := by
          change Function.update v j (!v j) i = v i
          exact Function.update_of_ne hij _ _
        simp [chunkOnes, hflip, hij]
    simp [chunkCount, hset, hj]

/-- A flip outside a chunk leaves its binned count unchanged. -/
theorem key_first_flip_eq_of_not_mem_chunk (v : CubeVertex n) (j : Fin n) (r : Fin s)
    (hnot : j ∉ Γ.chunk r) :
    (Γ.key (cubeFlip v j)).1 r = (Γ.key v).1 r := by
  have hdist := Γ.chunkCount_flip_dist r v j
  rw [if_neg hnot] at hdist
  have hcount : chunkCount Γ r v = chunkCount Γ r (cubeFlip v j) :=
    Nat.eq_of_dist_eq_zero (by simpa using hdist)
  have hindex : chunkIndex Γ r v = chunkIndex Γ r (cubeFlip v j) := Fin.ext hcount
  rw [Γ.key_first_apply (cubeFlip v j) r, Γ.key_first_apply v r, hindex]

/-- A coordinate flip changes the grid key by at most one grid edge. -/
theorem keyDist_flip_le_one (v : CubeVertex n) (j : Fin n) :
    Γ.keyDist (Γ.key v).1 (Γ.key (cubeFlip v j)).1 ≤ 1 := by
  classical
  let g := (Γ.key v).1
  let h := (Γ.key (cubeFlip v j)).1
  have hterm (r : Fin s) : Nat.dist (g r).val (h r).val ≤ 1 := by
    have hcounts :
        Nat.dist (chunkIndex Γ r v).val (chunkIndex Γ r (cubeFlip v j)).val ≤ 1 := by
      have h := Γ.chunkCount_flip_dist r v j
      by_cases hj : j ∈ Γ.chunk r <;> simp [chunkIndex, h, hj]
    have hbin := Γ.bin_dist_le_one_of_count_dist r
      (chunkIndex Γ r v) (chunkIndex Γ r (cubeFlip v j)) hcounts
    change Nat.dist ((Γ.key v).1 r).val ((Γ.key (cubeFlip v j)).1 r).val ≤ 1
    rw [Γ.key_first_apply v r, Γ.key_first_apply (cubeFlip v j) r]
    exact hbin
  by_cases hchunk : ∃ r, j ∈ Γ.chunk r
  · obtain ⟨r, hr⟩ := hchunk
    have hother (r' : Fin s) (hne : r' ≠ r) : Nat.dist (g r').val (h r').val = 0 := by
      have hnot : j ∉ Γ.chunk r' := by
        intro hr'
        have hd :=
          (Finset.disjoint_left.mp (Γ.chunks_disjoint (Ne.symm hne)) hr hr')
        exact hd
      have heq := Γ.key_first_flip_eq_of_not_mem_chunk v j r' hnot
      simp [g, h, heq]
    have hzeros :
        (∑ r' ∈ Finset.univ.erase r, Nat.dist (g r').val (h r').val) = 0 := by
      apply Finset.sum_eq_zero
      intro r' hr'
      exact hother r' (Finset.ne_of_mem_erase hr')
    have hsum : Γ.keyDist g h = Nat.dist (g r).val (h r).val := by
      calc
        Γ.keyDist g h = Nat.dist (g r).val (h r).val +
            ∑ r' ∈ Finset.univ.erase r, Nat.dist (g r').val (h r').val := by
          unfold GridGeom.keyDist
          exact (Finset.add_sum_erase Finset.univ
            (fun i => Nat.dist (g i).val (h i).val) (Finset.mem_univ r)).symm
        _ = Nat.dist (g r).val (h r).val := by simp [hzeros]
    rw [hsum]
    exact hterm r
  · have hkeys : g = h := by
      funext r
      have hnot : j ∉ Γ.chunk r := by
        intro hr
        exact hchunk ⟨r, hr⟩
      exact (Γ.key_first_flip_eq_of_not_mem_chunk v j r hnot).symm
    simp [GridGeom.keyDist, g, h, hkeys]

/-- An auxiliary flip changes exactly the corresponding bit of the auxiliary word. -/
theorem key_auxDist_flip (v : CubeVertex n) (j : Fin n) :
    Γ.auxDist (Γ.key v).2 (Γ.key (cubeFlip v j)).2 =
      if j ∈ Γ.aux then 1 else 0 := by
  classical
  by_cases hj : j ∈ Γ.aux
  · let jaux : Γ.aux := ⟨j, hj⟩
    have hset :
        (Finset.univ.filter fun i : Γ.aux => v i.1 ≠ cubeFlip v j i.1) = {jaux} := by
      ext i
      by_cases hi : i.1 = j
      · have hieq : i = jaux := by apply Subtype.ext; exact hi
        subst i
        have hflipj : cubeFlip v j j = !v j := by
          change Function.update v j (!v j) j = !v j
          exact Function.update_self j (!v j) v
        cases hv : v j <;> simp [jaux, hflipj, hv]
      · have hsame : cubeFlip v j i.1 = v i.1 := by
          change Function.update v j (!v j) i.1 = v i.1
          exact Function.update_of_ne hi _ _
        have hne : i ≠ jaux := by
          intro heq
          exact hi (congrArg Subtype.val heq)
        simp [hsame, hne]
    simp only [GridGeom.key]
    simp [GridGeom.auxDist, hset, hj]
  · have heq : (Γ.key (cubeFlip v j)).2 = (Γ.key v).2 := by
      simp only [GridGeom.key]
      funext i
      have hi : i.1 ≠ j := by
        intro hij
        exact hj (hij ▸ i.2)
      simp [cubeFlip, Function.update_of_ne hi]
    rw [heq]
    simp [GridGeom.auxDist, hj]

/-- The product cell moves by at most one edge under a coordinate flip. -/
theorem cellDist_flip_le_one (v : CubeVertex n) (j : Fin n) :
    Γ.cellDist (Γ.key v) (Γ.key (cubeFlip v j)) ≤ 1 := by
  classical
  have hkey : Γ.keyDist (Γ.key v).1 (Γ.key (cubeFlip v j)).1 ≤ 1 :=
    Γ.keyDist_flip_le_one v j
  by_cases hj : j ∈ Γ.aux
  · have hkeyeq : (Γ.key v).1 = (Γ.key (cubeFlip v j)).1 := by
      funext r
      have hnot : j ∉ Γ.chunk r := by
        intro hr
        exact (Finset.disjoint_left.mp (Γ.aux_disjoint r) hj hr)
      exact (Γ.key_first_flip_eq_of_not_mem_chunk v j r hnot).symm
    have hkey0 : Γ.keyDist (Γ.key v).1 (Γ.key (cubeFlip v j)).1 = 0 := by
      simp [GridGeom.keyDist, hkeyeq]
    rw [GridGeom.cellDist, hkey0, Γ.key_auxDist_flip, if_pos hj]
  · have haux0 : Γ.auxDist (Γ.key v).2 (Γ.key (cubeFlip v j)).2 = 0 := by
      rw [Γ.key_auxDist_flip, if_neg hj]
    rw [GridGeom.cellDist, haux0]
    exact hkey

/-- The integer-coordinate grid metric has a one-edge geodesic predecessor. -/
theorem keyDist_geodesic (g h : Γ.Key) (hne : 0 < Γ.keyDist g h) :
    ∃ z, Γ.keyDist g z + 1 = Γ.keyDist g h ∧ Γ.keyDist z h = 1 := by
  classical
  have hsumpos : 0 < ∑ r, Nat.dist (g r).val (h r).val := by
    simpa [GridGeom.keyDist] using hne
  obtain ⟨r, _, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega :
    (∑ r, Nat.dist (g r).val (h r).val) ≠ 0)
  have hdiff : (g r).val ≠ (h r).val := by
    intro heq
    apply hrne
    simp [heq]
  by_cases hlt : (h r).val < (g r).val
  · let v : Fin (Γ.bins r) := ⟨(h r).val + 1, by omega⟩
    let z : Γ.Key := Function.update h r v
    have hmove : Nat.dist (g r).val v.val + 1 = Nat.dist (g r).val (h r).val := by
      have hvle : v.val ≤ (g r).val := by simp [v]; omega
      have hhle : (h r).val ≤ (g r).val := Nat.le_of_lt hlt
      rw [Nat.dist_eq_sub_of_le_right hvle, Nat.dist_eq_sub_of_le_right hhle]
      simp [v]
      omega
    have hstep : Nat.dist v.val (h r).val = 1 := by
      have hle : (h r).val ≤ v.val := by simp [v]
      rw [Nat.dist_eq_sub_of_le_right hle]
      norm_num [v]
    have hsplit (a k : Γ.Key) :
        Γ.keyDist a k = Nat.dist (a r).val (k r).val +
          ∑ i ∈ Finset.univ.erase r, Nat.dist (a i).val (k i).val := by
      unfold GridGeom.keyDist
      exact (Finset.add_sum_erase Finset.univ
        (fun i => Nat.dist (a i).val (k i).val) (Finset.mem_univ r)).symm
    have hother :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (z i).val) =
          ∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (h i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    have hother' :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (z i).val (h i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    refine ⟨z, ?_, ?_⟩
    · rw [hsplit g z, hsplit g h, hother]
      simp only [z, Function.update_self]
      omega
    · rw [hsplit z h, hother']
      simpa [z, Function.update_self] using hstep
  · have hlt' : (g r).val < (h r).val := by omega
    let v : Fin (Γ.bins r) := ⟨(h r).val - 1, by omega⟩
    let z : Γ.Key := Function.update h r v
    have hmove : Nat.dist (g r).val v.val + 1 = Nat.dist (g r).val (h r).val := by
      have hgle : (g r).val ≤ v.val := by simp [v]; omega
      have hghle : (g r).val ≤ (h r).val := Nat.le_of_lt hlt'
      rw [Nat.dist_eq_sub_of_le hgle, Nat.dist_eq_sub_of_le hghle]
      simp [v]
      omega
    have hstep : Nat.dist v.val (h r).val = 1 := by
      have hle : v.val ≤ (h r).val := by simp [v]
      rw [Nat.dist_eq_sub_of_le hle]
      norm_num [v]
      omega
    have hsplit (a k : Γ.Key) :
        Γ.keyDist a k = Nat.dist (a r).val (k r).val +
          ∑ i ∈ Finset.univ.erase r, Nat.dist (a i).val (k i).val := by
      unfold GridGeom.keyDist
      exact (Finset.add_sum_erase Finset.univ
        (fun i => Nat.dist (a i).val (k i).val) (Finset.mem_univ r)).symm
    have hother :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (z i).val) =
          ∑ i ∈ Finset.univ.erase r, Nat.dist (g i).val (h i).val := by
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    have hother' :
        (∑ i ∈ Finset.univ.erase r, Nat.dist (z i).val (h i).val) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hir : i ≠ r := Finset.ne_of_mem_erase hi
      simp [z, Function.update_of_ne hir]
    refine ⟨z, ?_, ?_⟩
    · rw [hsplit g z, hsplit g h, hother]
      simp only [z, Function.update_self]
      omega
    · rw [hsplit z h, hother']
      simpa [z, Function.update_self] using hstep

/-- A key has at most two distance-one neighbors per coordinate. -/
theorem keyNbrs_card_le (g : Γ.Key) : (Γ.keyNbrs g).card ≤ 2 * s := by
  classical
  let up (k : Γ.Key) (r : Fin s) : Γ.Key :=
    if h : (k r).val + 1 < Γ.bins r then
      Function.update k r ⟨(k r).val + 1, h⟩ else k
  let down (k : Γ.Key) (r : Fin s) : Γ.Key :=
    if h : 0 < (k r).val then
      Function.update k r ⟨(k r).val - 1, by omega⟩ else k
  let candidates := (Finset.univ.image (up g)) ∪ (Finset.univ.image (down g))
  have hsub : Γ.keyNbrs g ⊆ candidates := by
    intro h hh
    have hdist : Γ.keyDist g h = 1 := by simpa [GridGeom.keyNbrs] using hh
    let f : Fin s → ℕ := fun i => Nat.dist (g i).val (h i).val
    have hsum : (∑ i ∈ Finset.univ, f i) = 1 := by
      simpa [f, GridGeom.keyDist] using hdist
    obtain ⟨r, _, hrne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega :
      (∑ i ∈ Finset.univ, f i) ≠ 0)
    have hrone : f r = 1 := by
      have hle : f r ≤ 1 := by
        calc
          f r ≤ ∑ i ∈ Finset.univ, f i :=
            Finset.single_le_sum (fun i hi => Nat.zero_le _) (Finset.mem_univ r)
          _ = 1 := hsum
      omega
    have hsumErase : f r + ∑ i ∈ Finset.univ.erase r, f i = 1 := by
      calc
        f r + ∑ i ∈ Finset.univ.erase r, f i = ∑ i ∈ Finset.univ, f i :=
          Finset.add_sum_erase Finset.univ f (Finset.mem_univ r)
        _ = 1 := hsum
    have hsumOther : (∑ i ∈ Finset.univ.erase r, f i) = 0 := by
      rw [hrone] at hsumErase
      omega
    have hother_zero (i : Fin s) (hi : i ∈ Finset.univ.erase r) : f i = 0 := by
      have hle : f i ≤ ∑ j ∈ Finset.univ.erase r, f j :=
        Finset.single_le_sum (fun j hj => Nat.zero_le _) hi
      rw [hsumOther] at hle
      omega
    have hchanged : (g r).val ≠ (h r).val := by
      intro heq
      apply hrne
      simp [f, heq]
    by_cases hlt : (g r).val < (h r).val
    · have hval : (h r).val = (g r).val + 1 := by
        have hd := hrone
        dsimp [f] at hd
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)] at hd
        omega
      have hbound : (g r).val + 1 < Γ.bins r := by omega
      have heq : h = Function.update g r ⟨(g r).val + 1, hbound⟩ := by
        funext i
        by_cases hir : i = r
        · subst i
          apply Fin.ext
          simp [hval]
        · have hi : i ∈ Finset.univ.erase r := by simp [hir]
          have hval0 : (g i).val = (h i).val := by
            exact Nat.eq_of_dist_eq_zero (by simpa [f] using hother_zero i hi)
          apply Fin.ext
          simp [Function.update_of_ne hir, hval0]
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      refine ⟨r, Finset.mem_univ _, ?_⟩
      simpa [up, hbound] using heq.symm
    · have hlt' : (h r).val < (g r).val := by omega
      have hval : (g r).val = (h r).val + 1 := by
        have hd := hrone
        dsimp [f] at hd
        rw [Nat.dist_eq_sub_of_le_right (Nat.le_of_lt hlt')] at hd
        omega
      have hpositive : 0 < (g r).val := by omega
      have heq : h = Function.update g r ⟨(g r).val - 1, by omega⟩ := by
        funext i
        by_cases hir : i = r
        · subst i
          apply Fin.ext
          simp [hval]
        · have hi : i ∈ Finset.univ.erase r := by simp [hir]
          have hval0 : (g i).val = (h i).val := by
            exact Nat.eq_of_dist_eq_zero (by simpa [f] using hother_zero i hi)
          apply Fin.ext
          simp [Function.update_of_ne hir, hval0]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨r, Finset.mem_univ _, ?_⟩
      simpa [down, hpositive] using heq.symm
  have hcard : candidates.card ≤ 2 * s := by
    calc
      candidates.card ≤ (Finset.univ.image (up g)).card +
          (Finset.univ.image (down g)).card := Finset.card_union_le _ _
      _ ≤ (Finset.univ : Finset (Fin s)).card +
          (Finset.univ : Finset (Fin s)).card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ = 2 * s := by simp [Fintype.card_fin]; omega
  exact (Finset.card_le_card hsub).trans hcard

/-- Auxiliary Hamming distance is zero exactly on equal words. -/
theorem auxDist_eq_zero_iff (t t' : Γ.AuxWord) : Γ.auxDist t t' = 0 ↔ t = t' := by
  classical
  constructor
  · intro h
    funext j
    by_contra hne
    have hj : j ∈ Finset.univ.filter fun i => t i ≠ t' i := by simp [hne]
    have hpos : 0 < (Finset.univ.filter fun i => t i ≠ t' i).card :=
      Finset.card_pos.mpr ⟨j, hj⟩
    have hcard : (Finset.univ.filter fun i => t i ≠ t' i).card = 0 := by
      simpa [GridGeom.auxDist] using h
    omega
  · intro h
    subst t'
    simp [GridGeom.auxDist]

/-- Auxiliary Hamming distance has a one-coordinate geodesic predecessor. -/
theorem auxDist_geodesic (t t' : Γ.AuxWord) (hne : 0 < Γ.auxDist t t') :
    ∃ z, Γ.auxDist t z + 1 = Γ.auxDist t t' ∧ Γ.auxDist z t' = 1 := by
  classical
  have hpos : 0 < (Finset.univ.filter fun j => t j ≠ t' j).card := by
    simpa [GridGeom.auxDist] using hne
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  have hbit : t j ≠ t' j := (Finset.mem_filter.mp hj).2
  let z : Γ.AuxWord := Function.update t' j (t j)
  have hfilter :
      (Finset.univ.filter fun i => t i ≠ z i) =
        (Finset.univ.filter fun i => t i ≠ t' i).erase j := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [z]
    · simp [z, Function.update_of_ne hij, hij]
  have hsingle : (Finset.univ.filter fun i => z i ≠ t' i) = {j} := by
    ext i
    by_cases hij : i = j
    · subst i
      simp [z, hbit]
    · simp [z, Function.update_of_ne hij, hij]
  refine ⟨z, ?_, ?_⟩
  · unfold GridGeom.auxDist
    rw [hfilter]
    exact Finset.card_erase_add_one hj
  · simp [GridGeom.auxDist, hsingle]

/-- The radius-one ball of auxiliary words consists of its center and one flip per auxiliary bit. -/
theorem auxBall_one_card_q_s07_geom (t : Γ.AuxWord) :
    (Γ.auxBall t 1).card = q + 1 := by
  classical
  let flip : Γ.aux → Γ.AuxWord := fun j => Function.update t j (!(t j))
  let flips : Finset Γ.AuxWord := Finset.univ.image flip
  have hflipdist (j : Γ.aux) : Γ.auxDist t (flip j) = 1 := by
    have hset : (Finset.univ.filter fun i => t i ≠ flip j i) = {j} := by
      ext i
      by_cases hij : i = j
      · subst i
        simp [flip]
      · have hsame : flip j i = t i := by
          change Function.update t j (!(t j)) i = t i
          exact Function.update_of_ne hij _ _
        simp [hsame, hij]
    simp [GridGeom.auxDist, hset]
  have hinj : Function.Injective flip := by
    intro i j hij
    by_contra hne
    have hval := congrArg (fun f : Γ.aux → Bool => f i) hij
    have hleft : flip i i = !t i := by simp [flip]
    have hright : flip j i = t i := by
      change Function.update t j (!(t j)) i = t i
      exact Function.update_of_ne hne _ _
    rw [hleft, hright] at hval
    cases hi : t i <;> simp [hi] at hval
  have hnot : t ∉ flips := by
    intro ht
    rcases Finset.mem_image.mp ht with ⟨j, -, heq⟩
    have hval := congrArg (fun f : Γ.aux → Bool => f j) heq
    have hflip : flip j j = !t j := by simp [flip]
    rw [hflip] at hval
    cases hj : t j <;> simp [hj] at hval
  have hball : Γ.auxBall t 1 = insert t flips := by
    ext w
    constructor
    · intro hw
      have hd : Γ.auxDist t w ≤ 1 := (Finset.mem_filter.mp hw).2
      by_cases heq : w = t
      · exact Finset.mem_insert.mpr (Or.inl heq)
      · have hne0 : Γ.auxDist t w ≠ 0 := by
          intro h0
          exact heq ((Γ.auxDist_eq_zero_iff t w).mp h0).symm
        obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
        have hdist1 : Γ.auxDist t w = 1 := by omega
        have hcard1 : (Finset.univ.filter fun i => t i ≠ w i).card = 1 := by
          simpa [GridGeom.auxDist] using hdist1
        obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hcard1
        have hjEq : j₀ = j := by
          have hjmem : j ∈ Finset.univ.filter fun i => t i ≠ w i := hj
          rw [hj₀] at hjmem
          exact (Finset.mem_singleton.mp hjmem).symm
        have hfilter : (Finset.univ.filter fun i => t i ≠ w i) = {j} := by
          simpa [hjEq] using hj₀
        have hbit : w j = !t j := by
          have hdiff := (Finset.mem_filter.mp hj).2
          cases ht : t j <;> cases hwj : w j <;> simp_all
        have hsame (i : Γ.aux) (hij : i ≠ j) : w i = t i := by
          have hnotDiff : ¬ (t i ≠ w i) := by
            intro hdiff
            have hi : i ∈ Finset.univ.filter fun k => t k ≠ w k := by simp [hdiff]
            have : i = j := by simpa [hfilter] using hi
            exact hij this
          cases ht : t i <;> cases hwj : w i <;> simp_all
        have heqFlip : w = flip j := by
          funext i
          by_cases hij : i = j
          · subst i
            simp [flip, hbit]
          · simp [flip, Function.update_of_ne hij, hsame i hij]
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_image.mpr
        exact ⟨j, Finset.mem_univ _, heqFlip.symm⟩
    · intro hw
      rcases Finset.mem_insert.mp hw with hwt | hw
      · subst w
        simp [GridGeom.auxBall, GridGeom.auxDist]
      · rcases Finset.mem_image.mp hw with ⟨j, -, rfl⟩
        simp [GridGeom.auxBall, hflipdist j]
  calc
    (Γ.auxBall t 1).card = (insert t flips).card := congrArg Finset.card hball
    _ = flips.card + 1 := Finset.card_insert_of_notMem hnot
    _ = (Finset.univ : Finset Γ.aux).card + 1 := by
      change (Finset.univ.image flip).card + 1 = _
      rw [Finset.card_image_of_injective _ hinj]
    _ = q + 1 := by simp [Γ.aux_card]

/-- The number of chunk bit words with a fixed bin is the binomial sum defining its mass. -/
theorem chunkPatternCard_q_s07_geom (r : Fin s) (b : Fin (Γ.bins r)) :
    (Finset.univ.filter fun f : Γ.chunk r → Bool =>
      Γ.bin r (chunkPatternIndex_q_s07_geom Γ r f) = b).card =
      ∑ k : Fin (ℓ + 1),
        if Γ.bin r k = b then Nat.choose ℓ k.val else 0 := by
  classical
  let e := boolFinsetEquiv (Γ.chunk r)
  let goodF := Finset.univ.filter fun f : Γ.chunk r → Bool =>
    Γ.bin r (chunkPatternIndex_q_s07_geom Γ r f) = b
  let sizeIndex := fun A : Finset (Γ.chunk r) =>
    (⟨A.card, Nat.lt_succ_of_le (by
      calc
        A.card ≤ (Finset.univ : Finset (Γ.chunk r)).card :=
          Finset.card_le_card (Finset.subset_univ A)
        _ = ℓ := by simp [Γ.chunk_card r])⟩ : Fin (ℓ + 1))
  let goodS := Finset.univ.filter fun A : Finset (Γ.chunk r) => Γ.bin r (sizeIndex A) = b
  have himage : goodF.image e = goodS := by
    ext A
    constructor
    · intro hA
      rcases Finset.mem_image.mp hA with ⟨f, hf, rfl⟩
      have hidx : chunkPatternIndex_q_s07_geom Γ r f = sizeIndex (e f) := by
        apply Fin.ext
        simp [chunkPatternIndex_q_s07_geom, sizeIndex, e, boolFinsetEquiv]
      have hbin : Γ.bin r (sizeIndex (e f)) = b := by
        simpa [hidx] using (Finset.mem_filter.mp hf).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbin⟩
    · intro hA
      have hbin := (Finset.mem_filter.mp hA).2
      let f := e.symm A
      have hidx : chunkPatternIndex_q_s07_geom Γ r f = sizeIndex A := by
        apply Fin.ext
        have hfilter :
            Finset.univ.filter (fun x : Γ.chunk r => (e.symm A) x = true) = A := by
          ext x
          simp [e, boolFinsetEquiv]
        change (Finset.univ.filter fun x : Γ.chunk r => (e.symm A) x = true).card = A.card
        rw [hfilter]
      apply Finset.mem_image.mpr
      refine ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [hidx] using hbin
      · simp [f, e]
  have hcardImage : goodF.card = goodS.card := by
    rw [← himage, Finset.card_image_of_injective _ e.injective]
  have hmaps : (goodS : Set (Finset (Γ.chunk r))).MapsTo sizeIndex
      (Finset.univ : Finset (Fin (ℓ + 1))) := by
    intro A hA
    exact Finset.mem_univ _
  have hcardFibers := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (k : Fin (ℓ + 1)) :
      (goodS.filter fun A => sizeIndex A = k).card =
        if Γ.bin r k = b then Nat.choose ℓ k.val else 0 := by
    by_cases hbin : Γ.bin r k = b
    · have heq : goodS.filter (fun A => sizeIndex A = k) =
          (Finset.univ : Finset (Γ.chunk r)).powersetCard k.val := by
        ext A
        simp only [goodS, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powersetCard]
        constructor
        · rintro ⟨hA, hsize⟩
          constructor
          · exact Finset.subset_univ _
          · have hval := congrArg Fin.val hsize
            simpa [sizeIndex] using hval
        · rintro ⟨hsub, hcard⟩
          have hsize : sizeIndex A = k := by
            apply Fin.ext
            simpa [sizeIndex] using hcard
          exact ⟨by simpa [hsize] using hbin, hsize⟩
      rw [heq, Finset.card_powersetCard]
      simp [Γ.chunk_card r, hbin]
    · have heq : goodS.filter (fun A => sizeIndex A = k) = ∅ := by
        ext A
        constructor
        · intro hmem
          rcases Finset.mem_filter.mp hmem with ⟨hA, hsize⟩
          have hbin' : Γ.bin r (sizeIndex A) = b := (Finset.mem_filter.mp hA).2
          rw [hsize] at hbin'
          exact (hbin hbin').elim
        · intro hmem
          exact False.elim (Finset.notMem_empty A hmem)
      rw [heq]
      simp [hbin]
  rw [hcardImage]
  calc
    goodS.card = ∑ k : Fin (ℓ + 1), (goodS.filter fun A => sizeIndex A = k).card := by
      simpa using hcardFibers
    _ = _ := by simp_rw [hfiber]

/-- Grid distance is zero exactly on equal keys. -/
theorem keyDist_eq_zero_iff (g h : Γ.Key) : Γ.keyDist g h = 0 ↔ g = h := by
  classical
  constructor
  · intro hz
    funext r
    have hle : Nat.dist (g r).val (h r).val ≤ Γ.keyDist g h := by
      unfold GridGeom.keyDist
      exact Finset.single_le_sum
        (fun i hi => Nat.zero_le (Nat.dist (g i).val (h i).val))
        (Finset.mem_univ r)
    have hdist : Nat.dist (g r).val (h r).val = 0 := by simpa [hz] using hle
    exact Fin.ext (Nat.eq_of_dist_eq_zero hdist)
  · rintro rfl
    simp [GridGeom.keyDist]

/-- The distance-one auxiliary neighbors are counted by the radius-one ball minus its center. -/
theorem auxNbrs_card_of_auxBall_one_card (t : Γ.AuxWord)
    (hball : (Γ.auxBall t 1).card = q + 1) :
    (Finset.univ.filter fun t' => Γ.auxDist t t' = 1).card = q := by
  classical
  let nbrs := Finset.univ.filter fun t' : Γ.AuxWord => Γ.auxDist t t' = 1
  have hdecomp : Γ.auxBall t 1 = insert t nbrs := by
    ext t'
    simp only [GridGeom.auxBall, nbrs, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro h
      by_cases heq : t' = t
      · exact Or.inl heq
      · right
        have hne0 : Γ.auxDist t t' ≠ 0 := by
          intro h0
          exact heq ((Γ.auxDist_eq_zero_iff t t').mp h0).symm
        omega
    · rintro (rfl | h)
      · simp [GridGeom.auxDist]
      · omega
  have hnot : t ∉ nbrs := by simp [nbrs, GridGeom.auxDist]
  have hcardInsert : (insert t nbrs).card = nbrs.card + 1 :=
    Finset.card_insert_of_notMem hnot
  rw [hdecomp, hcardInsert] at hball
  exact Nat.add_right_cancel hball

/-- Product cell distance has a one-edge geodesic predecessor. -/
theorem cellDist_geodesic (c c' : Γ.Cell) (hne : 0 < Γ.cellDist c c') :
    ∃ z, Γ.cellDist c z + 1 = Γ.cellDist c c' ∧ Γ.cellDist z c' = 1 := by
  classical
  by_cases hk : 0 < Γ.keyDist c.1 c'.1
  · obtain ⟨g, hg, hgm⟩ := Γ.keyDist_geodesic c.1 c'.1 hk
    let z : Γ.Cell := (g, c'.2)
    refine ⟨z, ?_, ?_⟩
    · simp [GridGeom.cellDist, z]
      omega
    · simpa [GridGeom.cellDist, z, GridGeom.auxDist] using hgm
  · have hk0 : Γ.keyDist c.1 c'.1 = 0 := Nat.eq_zero_of_not_pos hk
    have heq : c.1 = c'.1 := (Γ.keyDist_eq_zero_iff c.1 c'.1).mp hk0
    have ha : 0 < Γ.auxDist c.2 c'.2 := by
      have hsum : 0 < Γ.keyDist c.1 c'.1 + Γ.auxDist c.2 c'.2 := by
        simpa [GridGeom.cellDist] using hne
      omega
    obtain ⟨t, ht, htm⟩ := Γ.auxDist_geodesic c.2 c'.2 ha
    let z : Γ.Cell := (c.1, t)
    refine ⟨z, ?_, ?_⟩
    · have hkey : Γ.keyDist c.1 c'.1 = 0 := hk0
      simpa [GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist, z, heq] using ht
    · simpa [GridGeom.cellDist, GridGeom.keyDist, GridGeom.auxDist, z, heq] using htm

/-- A cell has at most the key-neighbor and auxiliary-neighbor choices. -/
theorem cellNbrs_card_le (c : Γ.Cell)
    (hball : ∀ t : Γ.AuxWord, (Γ.auxBall t 1).card = q + 1) :
    (Finset.univ.filter fun c' => Γ.cellDist c c' = 1).card ≤ 2 * s + q := by
  classical
  let anbr (t : Γ.AuxWord) := Finset.univ.filter fun t' => Γ.auxDist t t' = 1
  let cross := (Γ.keyNbrs c.1).image fun g => (g, c.2)
  let own := (anbr c.2).image fun t => (c.1, t)
  have hsub : (Finset.univ.filter fun c' => Γ.cellDist c c' = 1) ⊆ cross ∪ own := by
    intro c' hc'
    have hdist' : Γ.cellDist c c' = 1 := (Finset.mem_filter.mp hc').2
    rcases c' with ⟨g', t'⟩
    have hdist : Γ.keyDist c.1 g' + Γ.auxDist c.2 t' = 1 := by
      simpa [GridGeom.cellDist] using hdist'
    by_cases hk : Γ.keyDist c.1 g' = 1
    · have ha : Γ.auxDist c.2 t' = 0 := by omega
      have hteq : c.2 = t' := (Γ.auxDist_eq_zero_iff c.2 t').mp ha
      have hkmem : g' ∈ Γ.keyNbrs c.1 := by simpa [GridGeom.keyNbrs] using hk
      apply Finset.mem_union.mpr
      left
      apply Finset.mem_image.mpr
      exact ⟨g', hkmem, by simp [hteq]⟩
    · have hk0 : Γ.keyDist c.1 g' = 0 := by omega
      have ha : Γ.auxDist c.2 t' = 1 := by omega
      have hgeq : c.1 = g' := (Γ.keyDist_eq_zero_iff c.1 g').mp hk0
      have htm : t' ∈ anbr c.2 := by simp [anbr, ha]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      exact ⟨t', htm, by simp [hgeq]⟩
  have hanbr : (anbr c.2).card = q :=
    Γ.auxNbrs_card_of_auxBall_one_card c.2 (hball c.2)
  calc
    (Finset.univ.filter fun c' => Γ.cellDist c c' = 1).card ≤ (cross ∪ own).card :=
      Finset.card_le_card hsub
    _ ≤ cross.card + own.card := Finset.card_union_le _ _
    _ ≤ (Γ.keyNbrs c.1).card + (anbr c.2).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ ≤ 2 * s + q := Nat.add_le_add (Γ.keyNbrs_card_le c.1) (by omega)

end GridGeom

end HypercubeRamsey.S07
