import HypercubeRamsey.S09.Needs
import HypercubeRamsey.S09.Core.Defs
import HypercubeRamsey.Tools.CubeGeometry

namespace HypercubeRamsey

open OAI.HypercubeRamsey

private def syndrome7 (x : CubeVertex 7) : CubeVertex 3 := fun j =>
  decide (((Finset.univ.filter fun i : Fin 7 =>
    x i && Nat.testBit (i.val + 1) j.val).card % 2) = 1)

private def syndromeMatch7 (x : CubeVertex 7) (s : CubeVertex 3) : Prop :=
  ∀ j, syndrome7 x j = s j

private instance (x : CubeVertex 7) (s : CubeVertex 3) :
    Decidable (syndromeMatch7 x s) := by
  unfold syndromeMatch7
  exact Fintype.decidableForallFintype

private def codeColor2 (s : CubeVertex 2) : CubeVertex 3 := fun j =>
  decide (j.val = 0) && s ⟨0, by omega⟩

private def join2x7 (s : CubeVertex 2) (q : CubeVertex 7) : CubeVertex 9 := fun i =>
  if h : i.val < 2 then s ⟨i.val, h⟩ else q ⟨i.val - 2, by omega⟩

private def center2x7 (s : CubeVertex 2) (q : CubeVertex 7) : CenterID9 2 9 1 :=
  ⟨s, join2x7 s q, 0⟩

private def active2x7 : Finset (CenterID9 2 9 1) :=
  (Finset.univ.filter fun p : CubeVertex 2 × CubeVertex 7 =>
    syndromeMatch7 p.2 (codeColor2 p.1)).image (fun p => center2x7 p.1 p.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem syndrome7_cover_unique :
    ∀ (t : CubeVertex 7) (s : CubeVertex 3),
      let near := Finset.univ.filter fun q : CubeVertex 7 =>
        syndromeMatch7 q s ∧ hammingDist q t ≤ 1
      near.Nonempty ∧ near.card ≤ 1 := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem syndrome7_radius_two (t : CubeVertex 7) (s : CubeVertex 3) :
    ((Finset.univ.filter fun q : CubeVertex 7 =>
      syndromeMatch7 q s ∧ hammingDist q t ≤ 2).card : ℕ) ≤ 4 := by
  decide +revert

private def tail9 (v : CubeVertex 9) : CubeVertex 7 := fun i =>
  v ⟨i.val + 2, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem join_specialWord (s : CubeVertex 2) (q : CubeVertex 7) :
    specialWord9 (by omega) (join2x7 s q) = s := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem join_residualDistance (s : CubeVertex 2) (q t : CubeVertex 7) :
    residualDistance9 2 (join2x7 s q) (join2x7 s t) = hammingDist q t := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem active2x7_crowds (v : CubeVertex 9) :
    (((active2x7.filter fun id => id.slice = specialWord9 (by omega) v ∧
        residualDistance9 2 id.location v ≤ 1 ∧ Nat.dist id.level.val 0 ≤ 2).card : ℕ) ≤ 1) ∧
    (((active2x7.filter fun id => wordDistance9 id.slice (specialWord9 (by omega) v) = 1 ∧
        residualDistance9 2 id.location v ≤ 0 ∧ Nat.dist id.level.val 0 ≤ 2).card : ℕ) ≤ 1) ∧
    (((active2x7.filter fun id => id.slice = specialWord9 (by omega) v ∧
        residualDistance9 2 id.location v ≤ 2 ∧ Nat.dist id.level.val 0 ≤ 2).card : ℕ) ≤ 4) := by
  decide +revert

def map2CounterexampleParams : Params9 where
  xS := 1 / 20
  xD := 3 / 50
  hMinus := 1 / 25
  hPlus := 40001 / 1000000
  σ := 1 / 200000
  χ := 1 / 10000
  case := .lin (1 / 100000) (1 / 200) (1 / 10) (1 / 2)

theorem map2CounterexampleParams_valid : map2CounterexampleParams.Valid := by
  norm_num [map2CounterexampleParams, Params9.Valid, min_def]

private theorem two_log_two_gt_one : (1 : ℝ) < 2 * Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  linarith

private def prefix9 (v : CubeVertex 9) : CubeVertex 2 :=
  specialWord9 (by norm_num) v

private theorem split_join9 (v : CubeVertex 9) : join2x7 (prefix9 v) (tail9 v) = v := by
  funext i
  by_cases hi : i.val < 2
  · simp [join2x7, prefix9, tail9, specialWord9, hi]
  · have hv : i.val - 2 + 2 = i.val := by omega
    simp [join2x7, prefix9, tail9, specialWord9, hi, hv]

noncomputable def map2CounterexampleWitness : HeightWitness9 map2CounterexampleParams 9 where
  specialBits := 2
  specialBits_le := by norm_num
  specialBudget := by
    have hlog := two_log_two_gt_one
    change map2CounterexampleParams.Ss 9 < 2 * Real.log 2
    norm_num [Params9.Ss, map2CounterexampleParams]
    linarith
  radius := 1
  levels := 1
  levels_pos := by norm_num
  active := active2x7
  ε := 1 / 400000
  ε_pos := by norm_num
  ε_lt_σ := by norm_num [map2CounterexampleParams]
  height := fun _ => 0
  height_lt := by intro v; norm_num
  height_good := by
    intro v
    let s := prefix9 v
    let t := tail9 v
    have hcode := syndrome7_cover_unique t (codeColor2 s)
    change (Finset.univ.filter fun q : CubeVertex 7 =>
      syndromeMatch7 q (codeColor2 s) ∧ hammingDist q t ≤ 1).Nonempty ∧ _ at hcode
    rcases hcode with ⟨hnear, _hsmall⟩
    obtain ⟨q, hqmem⟩ := hnear
    have hq' := Finset.mem_filter.mp hqmem
    have hq : syndromeMatch7 q (codeColor2 s) := hq'.2.1
    have hqt : hammingDist q t ≤ 1 := hq'.2.2
    refine ⟨⟨center2x7 s q, ?_, ?_, ?_, rfl⟩, ?_, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨(s, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩, rfl⟩
    · dsimp [center2x7, s, prefix9]
    · rw [← split_join9 v]
      change residualDistance9 2 (join2x7 (prefix9 v) q)
        (join2x7 (prefix9 v) (tail9 v)) ≤ 1
      rw [join_residualDistance]
      exact hqt
    · have hc := active2x7_crowds v
      have hcard : ((active2x7.filter fun id => id.slice = prefix9 v ∧
          residualDistance9 2 id.location v ≤ 1 ∧ Nat.dist id.level.val 0 ≤ 2).card : ℝ) ≤ 1 :=
        by exact_mod_cast hc.1
      exact hcard.trans (Real.one_le_rpow (by norm_num) (by norm_num [map2CounterexampleParams]))
    · have hc := active2x7_crowds v
      have hcard : ((active2x7.filter fun id => wordDistance9 id.slice (prefix9 v) = 1 ∧
          residualDistance9 2 id.location v ≤ 0 ∧ Nat.dist id.level.val 0 ≤ 2).card : ℝ) ≤ 1 :=
        by exact_mod_cast hc.2.1
      exact hcard.trans (Real.one_le_rpow (by norm_num) (by norm_num [map2CounterexampleParams]))
    · have hc := active2x7_crowds v
      have hcard : ((active2x7.filter fun id => id.slice = prefix9 v ∧
          residualDistance9 2 id.location v ≤ 2 ∧ Nat.dist id.level.val 0 ≤ 2).card : ℝ) ≤ 4 :=
        by exact_mod_cast hc.2.2
      have hexp : (3 / 4 : ℝ) < 1 - (map2CounterexampleParams.σ : ℝ) + (1 / 400000 : ℝ) := by
        norm_num [map2CounterexampleParams]
      have hpow : 4 < (9 : ℝ) ^ (3 / 4 : ℝ) := by
        let x : ℝ := 9 ^ (3 / 4 : ℝ)
        have hx0 : 0 ≤ x := by dsimp [x]; positivity
        have hxpow : x ^ 4 = 729 := by
          calc
            x ^ 4 = ((9 : ℝ) ^ (3 / 4 : ℝ)) ^ (4 : ℝ) := by
              dsimp [x]
              exact (Real.rpow_natCast ((9 : ℝ) ^ (3 / 4 : ℝ)) 4).symm
            _ = (9 : ℝ) ^ ((3 / 4 : ℝ) * 4) :=
              (Real.rpow_mul (x := 9) (by norm_num) (3 / 4 : ℝ) (4 : ℝ)).symm
            _ = 729 := by norm_num
        by_contra hle
        have hle : x ≤ 4 := le_of_not_gt hle
        have hsq : x ^ 2 ≤ 16 := by
          calc x ^ 2 = x * x := by ring
            _ ≤ x * 4 := mul_le_mul_of_nonneg_left hle hx0
            _ ≤ 4 * 4 := mul_le_mul_of_nonneg_right hle (by norm_num)
            _ = 16 := by norm_num
        have hfour : x ^ 4 ≤ 256 := by
          calc x ^ 4 = x ^ 2 * x ^ 2 := by ring
            _ ≤ x ^ 2 * 16 := mul_le_mul_of_nonneg_left hsq (sq_nonneg x)
            _ ≤ 16 * 16 := mul_le_mul_of_nonneg_right hsq (by norm_num)
            _ = 256 := by norm_num
        norm_num [hxpow] at hfour
      have hpow' : 4 ≤ (9 : ℝ) ^ (1 - (map2CounterexampleParams.σ : ℝ) + (1 / 400000 : ℝ)) := by
        have hmono := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 9) hexp
        exact le_of_lt (lt_trans hpow hmono)
      exact hcard.trans hpow'
  distance_two_regular := by intro u v huv; simp

private def zeroSlice9 : CubeVertex 2 := fun _ => false
private def zeroTail9 : CubeVertex 7 := fun _ => false
private def baseEven9 : CubeVertex 9 := join2x7 zeroSlice9 zeroTail9
private def nextSlice9 : CubeVertex 2 := cubeFlip zeroSlice9 ⟨1, by omega⟩
private def oddNeighbor9 (i : Fin 7) : CubeVertex 9 :=
  cubeFlip baseEven9 ⟨i.val + 2, by omega⟩
private def secondEven9 (i : Fin 7) : CubeVertex 9 :=
  cubeFlip (oddNeighbor9 i) ⟨1, by omega⟩
private def baseID9 : CenterID9 2 9 1 := center2x7 zeroSlice9 zeroTail9
private def nextID9 : CenterID9 2 9 1 := center2x7 nextSlice9 zeroTail9

private def sameSliceBall1_9 (v : CubeVertex 9) : Finset (CenterID9 2 9 1) :=
  active2x7.filter fun id => id.slice = prefix9 v ∧
    residualDistance9 2 id.location v ≤ 1 ∧ Nat.dist id.level.val 0 ≤ 2

private theorem sameSliceBall1_9_card (v : CubeVertex 9) :
    (sameSliceBall1_9 v).card ≤ 1 := by
  change (active2x7.filter fun id => id.slice = specialWord9 (by omega) v ∧
    residualDistance9 2 id.location v ≤ 1 ∧ Nat.dist id.level.val 0 ≤ 2).card ≤ 1
  exact (active2x7_crowds v).1

private theorem nextSlice_active : nextID9 ∈ active2x7 := by
  apply Finset.mem_image.mpr
  refine ⟨(nextSlice9, zeroTail9), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  decide

private theorem baseSlice_active : baseID9 ∈ active2x7 := by
  apply Finset.mem_image.mpr
  refine ⟨(zeroSlice9, zeroTail9), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem oddNeighbor9_join (i : Fin 7) :
    oddNeighbor9 i = join2x7 zeroSlice9 (cubeFlip zeroTail9 i) := by
  decide +revert

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem secondEven9_join (i : Fin 7) :
    secondEven9 i = join2x7 nextSlice9 (cubeFlip zeroTail9 i) := by
  decide +revert

private theorem oddNeighbor9_injective : Function.Injective oddNeighbor9 := by
  decide +revert

private theorem map2Counterexample_chi_lt_two :
    (9 : ℝ) ^ (map2CounterexampleParams.χ : ℝ) < 2 := by
  have hχ : 0 < (map2CounterexampleParams.χ : ℝ) := by norm_num [map2CounterexampleParams]
  have hχ4 : 4 * (map2CounterexampleParams.χ : ℝ) < 1 := by
    norm_num [map2CounterexampleParams]
  calc
    (9 : ℝ) ^ (map2CounterexampleParams.χ : ℝ) <
        16 ^ (map2CounterexampleParams.χ : ℝ) :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hχ
    _ = 2 ^ (4 * (map2CounterexampleParams.χ : ℝ)) := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num [Real.rpow_natCast]]
      exact (Real.rpow_mul (x := 2) (by norm_num) (4 : ℝ)
        (map2CounterexampleParams.χ : ℝ)).symm
    _ < 2 := by
      calc
        2 ^ (4 * (map2CounterexampleParams.χ : ℝ)) < 2 ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hχ4
        _ = 2 := by simp

open Classical
/-- The frozen even-star core clause fails for the explicit `n=9` witness above. -/
theorem p92_map2_even_core_counterexample :
    ¬ ∃ c : CubeVertex 9 → CenterID9 2 9 1,
      (∀ v, (c v).slice = specialWord9 (by norm_num) v ∧
        residualDistance9 2 (c v).location v ≤ map2CounterexampleWitness.radius ∧
        (c v).level = map2CounterexampleWitness.height v ∧
        c v ∈ map2CounterexampleWitness.active) ∧
      (∀ v : CubeVertex 9, IsEvenRole v →
        ∃ C : Finset (CenterID9 2 9 1), c v ∈ C ∧
          (C.card : ℝ) ≤ (9 : ℝ) ^ (map2CounterexampleParams.χ : ℝ) ∧
          ∀ id, id ∉ C →
            ((Finset.univ.filter (fun b : CubeVertex 9 =>
              ¬ IsEvenRole b ∧ (cube 9).Adj v b ∧ id ∈ seenIDs9 c b)).card : ℕ) ≤
                map2CounterexampleWitness.radius + 3) := by
  classical
  rintro ⟨c, hmap, hcore⟩
  have hbaseEven : IsEvenRole baseEven9 := by
    simp [IsEvenRole, baseEven9, join2x7, zeroSlice9, zeroTail9]
  have hbaseSel := hmap baseEven9
  have hbaseLevel : (c baseEven9).level.val = 0 := by
    have h := congrArg Fin.val hbaseSel.2.2.1
    simpa [map2CounterexampleWitness] using h
  have hbaseMem : c baseEven9 ∈ sameSliceBall1_9 baseEven9 := by
    apply Finset.mem_filter.mpr
    refine ⟨hbaseSel.2.2.2, ?_⟩
    refine ⟨?_, ?_, by simp [hbaseLevel]⟩
    · simpa [sameSliceBall1_9, prefix9] using hbaseSel.1
    · simpa [map2CounterexampleWitness] using hbaseSel.2.1
  have hbaseIDMem : baseID9 ∈ sameSliceBall1_9 baseEven9 := by
    apply Finset.mem_filter.mpr
    refine ⟨baseSlice_active, ?_⟩
    refine ⟨?_, ?_, by simp [baseID9, center2x7]⟩
    · change zeroSlice9 = specialWord9 (by omega) (join2x7 zeroSlice9 zeroTail9)
      exact (join_specialWord zeroSlice9 zeroTail9).symm
    · change residualDistance9 2 (join2x7 zeroSlice9 zeroTail9)
        (join2x7 zeroSlice9 zeroTail9) ≤ 1
      rw [join_residualDistance]
      simp [hammingDist]
  have hcBase : c baseEven9 = baseID9 := by
    apply (Finset.card_le_one_iff.mp (sameSliceBall1_9_card baseEven9))
    · exact hbaseMem
    · exact hbaseIDMem

  have hselectedID (i : Fin 7) : c (secondEven9 i) = nextID9 := by
    have hsel := hmap (secondEven9 i)
    have hlevel : (c (secondEven9 i)).level.val = 0 := by
      have h := congrArg Fin.val hsel.2.2.1
      simpa [map2CounterexampleWitness] using h
    have hselectedMem : c (secondEven9 i) ∈ sameSliceBall1_9 (secondEven9 i) := by
      apply Finset.mem_filter.mpr
      refine ⟨hsel.2.2.2, ?_⟩
      refine ⟨?_, ?_, by simp [hlevel]⟩
      · simpa [sameSliceBall1_9, prefix9] using hsel.1
      · simpa [map2CounterexampleWitness] using hsel.2.1
    have hnextMem : nextID9 ∈ sameSliceBall1_9 (secondEven9 i) := by
      apply Finset.mem_filter.mpr
      refine ⟨nextSlice_active, ?_⟩
      refine ⟨?_, ?_, by simp [nextID9, center2x7]⟩
      · rw [secondEven9_join]
        change nextSlice9 = specialWord9 (by omega)
          (join2x7 nextSlice9 (cubeFlip zeroTail9 i))
        exact (join_specialWord nextSlice9 (cubeFlip zeroTail9 i)).symm
      · rw [secondEven9_join]
        change residualDistance9 2 (join2x7 nextSlice9 zeroTail9)
          (join2x7 nextSlice9 (cubeFlip zeroTail9 i)) ≤ 1
        rw [join_residualDistance]
        have hflip : hammingDist zeroTail9 (cubeFlip zeroTail9 i) = 1 := by
          have hAdj := cubeFlip_adj zeroTail9 i
          change hammingDist zeroTail9 (cubeFlip zeroTail9 i) = 1 at hAdj
          exact hAdj
        rw [hflip]
    apply (Finset.card_le_one_iff.mp (sameSliceBall1_9_card (secondEven9 i)))
    · exact hselectedMem
    · exact hnextMem

  have hodd (i : Fin 7) : ¬ IsEvenRole (oddNeighbor9 i) := by
    have hflip := cubeFlip_parity baseEven9 ⟨i.val + 2, by omega⟩
    have htmp : ¬ IsEvenRole (cubeFlip baseEven9 ⟨i.val + 2, by omega⟩) := by
      rw [hflip]
      simp [hbaseEven]
    simpa [oddNeighbor9] using htmp
  have hadjBase (i : Fin 7) : (cube 9).Adj baseEven9 (oddNeighbor9 i) := by
    simpa [oddNeighbor9] using cubeFlip_adj baseEven9 ⟨i.val + 2, by omega⟩
  have hseen (i : Fin 7) : nextID9 ∈ seenIDs9 c (oddNeighbor9 i) := by
    unfold seenIDs9
    apply Finset.mem_image.mpr
    refine ⟨secondEven9 i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa [secondEven9] using
        (cubeFlip_adj (oddNeighbor9 i) ⟨1, by omega⟩).symm
    · exact hselectedID i

  let reads : Finset (CubeVertex 9) := Finset.univ.filter fun b =>
    ¬ IsEvenRole b ∧ (cube 9).Adj baseEven9 b ∧ nextID9 ∈ seenIDs9 c b
  have hreadSubset : Finset.univ.image oddNeighbor9 ⊆ reads := by
    intro b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hodd i, hadjBase i, hseen i⟩⟩
  have himageCard : (Finset.univ.image oddNeighbor9).card = 7 := by
    rw [Finset.card_image_of_injective _ oddNeighbor9_injective]
    simp
  have hreads : 7 ≤ reads.card := by
    rw [← himageCard]
    exact Finset.card_le_card hreadSubset

  obtain ⟨C, hbaseC, hCsize, houtside⟩ := hcore baseEven9 hbaseEven
  rw [hcBase] at hbaseC
  have hnextC : nextID9 ∈ C := by
    by_contra hnot
    have h := houtside nextID9 hnot
    have h' : reads.card ≤ 4 := by
      simpa [reads, map2CounterexampleWitness] using h
    omega
  have hne : baseID9 ≠ nextID9 := by decide
  have hpair : ({baseID9, nextID9} : Finset (CenterID9 2 9 1)) ⊆ C := by
    intro id hid
    simp only [Finset.mem_insert, Finset.mem_singleton] at hid
    rcases hid with rfl | rfl
    · exact hbaseC
    · exact hnextC
  have hCnat : 2 ≤ C.card := by
    have h := Finset.card_le_card hpair
    simpa [hne] using h
  have hCreal : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hCnat
  have hχ := map2Counterexample_chi_lt_two
  linarith

end HypercubeRamsey
