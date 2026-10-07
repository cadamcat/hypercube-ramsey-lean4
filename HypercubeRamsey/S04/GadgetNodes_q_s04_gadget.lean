import HypercubeRamsey.S04.CoreLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_q_s04_gadget

open Classical Filter OAI.HypercubeRamsey
open HypercubeRamsey.S04

private theorem chunkCoords_below_specialNum {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)) {i : Fin n}
    (hi : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    i.val < HypercubeRamsey.S04.specialNum β γ n := by
  classical
  unfold HypercubeRamsey.S04.chunkCoords at hi
  rcases Finset.mem_filter.mp hi with ⟨_, ⟨hlo, hhi⟩⟩
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hgs : g.val * s + j.val + 1 ≤ (g.val + 1) * s := by
    rw [Nat.add_mul, one_mul]
    omega
  have hG : (g.val + 1) * s ≤ G * s := Nat.mul_le_mul_right s (Nat.succ_le_of_lt g.isLt)
  have hblock := Nat.mul_le_mul_right ℓ (hgs.trans hG)
  have hblock' : (g.val * s + j.val) * ℓ + ℓ ≤ G * s * ℓ := by
    simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_assoc, G, s, ℓ] using hblock
  have hhi' : i.val < (g.val * s + j.val) * ℓ + ℓ := by
    simpa [HypercubeRamsey.S04.chunkStart, G, s, ℓ] using hhi
  have hspec : HypercubeRamsey.S04.specialNum β γ n = G * s * ℓ := by
    simp [HypercubeRamsey.S04.specialNum, G, s, ℓ, Nat.mul_assoc]
  rw [hspec]
  omega

private theorem chunkCount_flip_eq {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n))
    (v : CubeVertex n) (i : Fin n)
    (hi : i ∉ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    HypercubeRamsey.S04.chunkCount β γ n g j (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.chunkCount β γ n g j v := by
  classical
  unfold HypercubeRamsey.S04.chunkCount
  congr 1
  apply Finset.filter_congr
  intro j' hj'
  by_cases hji : j' = i
  · subst j'
    exact False.elim (hi hj')
  · simp [HypercubeRamsey.cubeFlip, Function.update_of_ne hji]

private theorem chunkCount_flip_delta {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n))
    (v : CubeVertex n) (i : Fin n)
    (hi : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    (HypercubeRamsey.S04.chunkCount β γ n g j
        (HypercubeRamsey.cubeFlip v i) ≤
      HypercubeRamsey.S04.chunkCount β γ n g j v + 1) ∧
    (HypercubeRamsey.S04.chunkCount β γ n g j v ≤
      HypercubeRamsey.S04.chunkCount β γ n g j
        (HypercubeRamsey.cubeFlip v i) + 1) := by
  classical
  let C := HypercubeRamsey.S04.chunkCoords β γ n g j
  let A := C.filter fun k => v k = true
  let B := C.filter fun k => HypercubeRamsey.cubeFlip v i k = true
  have hmemA : i ∈ A ↔ v i = true := by
    simp [A, C, hi]
  by_cases hv : v i = true
  · have hfilter : B = A.erase i := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [A, B, C, hi, hv, HypercubeRamsey.cubeFlip]
      · have hflip : HypercubeRamsey.cubeFlip v i k = v k :=
          Function.update_of_ne hki _ _
        simp [A, B, C, hflip, hki]
    have hcard : B.card + 1 = A.card := by
      rw [hfilter]
      exact Finset.card_erase_add_one (hmemA.mpr hv)
    change B.card ≤ A.card + 1 ∧ A.card ≤ B.card + 1
    omega
  · have hfilter : B = insert i A := by
      ext k
      by_cases hki : k = i
      · subst k
        simp [A, B, C, hi, hv, HypercubeRamsey.cubeFlip]
      · have hflip : HypercubeRamsey.cubeFlip v i k = v k :=
          Function.update_of_ne hki _ _
        simp [A, B, C, hflip, hki]
    have hnot : i ∉ A := by
      simp [A, C, hi, hv]
    have hcard : B.card = A.card + 1 := by
      rw [hfilter, Finset.card_insert_of_notMem hnot]
    change B.card ≤ A.card + 1 ∧ A.card ≤ B.card + 1
    omega

private theorem minClip_lipschitz {a b lo cap : ℕ} (hab : a ≤ b) (hba : b ≤ a + 1) :
    min (a - lo) cap ≤ min (b - lo) cap ∧
      min (b - lo) cap ≤ min (a - lo) cap + 1 := by
  have hsub : a - lo ≤ b - lo := Nat.sub_le_sub_right hab lo
  have hgap : b - lo ≤ (a - lo) + 1 := by omega
  refine ⟨min_le_min hsub le_rfl, ?_⟩
  by_cases hc : cap ≤ a - lo
  · rw [Nat.min_eq_right hc]
    have hc' : cap ≤ b - lo := le_trans hc hsub
    rw [Nat.min_eq_right hc']
    omega
  · have ha : a - lo ≤ cap := Nat.le_of_not_ge hc
    rw [Nat.min_eq_left ha]
    by_cases hb : b - lo ≤ cap
    · rw [Nat.min_eq_left hb]
      omega
    · have hb' : cap ≤ b - lo := Nat.le_of_not_ge hb
      rw [Nat.min_eq_right hb']
      omega

private theorem clipped_flip_delta {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n))
    (v : CubeVertex n) (i : Fin n)
    (hi : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    (HypercubeRamsey.S04.clipped β γ n g j
        (HypercubeRamsey.cubeFlip v i) ≤ HypercubeRamsey.S04.clipped β γ n g j v + 1) ∧
    (HypercubeRamsey.S04.clipped β γ n g j v ≤ HypercubeRamsey.S04.clipped β γ n g j
        (HypercubeRamsey.cubeFlip v i) + 1) := by
  have hc := chunkCount_flip_delta g j v i hi
  unfold HypercubeRamsey.S04.clipped
  let lo := HypercubeRamsey.S04.chunkLen β γ n / 2 -
    HypercubeRamsey.S04.gadgetPower β γ n ^ 2 / 2
  let cap := HypercubeRamsey.S04.gadgetPower β γ n ^ 2
  by_cases hcnt : HypercubeRamsey.S04.chunkCount β γ n g j
      (HypercubeRamsey.cubeFlip v i) ≤ HypercubeRamsey.S04.chunkCount β γ n g j v
  · have h := minClip_lipschitz (lo := lo) (cap := cap) hcnt hc.2
    exact ⟨h.1.trans (Nat.le_add_right _ _), h.2⟩
  · have hcnt' : HypercubeRamsey.S04.chunkCount β γ n g j v ≤
        HypercubeRamsey.S04.chunkCount β γ n g j (HypercubeRamsey.cubeFlip v i) :=
      Nat.le_of_not_ge hcnt
    have h := minClip_lipschitz (lo := lo) (cap := cap) hcnt' hc.1
    exact ⟨h.2, h.1.trans (Nat.le_add_right _ _)⟩

private theorem gadgetOut_flip_eq {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (v : CubeVertex n) (i : Fin n)
    (hi : ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      i ∉ HypercubeRamsey.S04.chunkCoords β γ n g j) :
    HypercubeRamsey.S04.gadgetOut β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.gadgetOut β γ n g v := by
  classical
  have hclip : ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) =
        HypercubeRamsey.S04.clipped β γ n g j v := by
    intro j
    simp [HypercubeRamsey.S04.clipped, chunkCount_flip_eq g j v i (hi j)]
  have hfun :
      (fun j : Fin (HypercubeRamsey.S04.chunkNum β γ n) =>
        HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i)) =
      (fun j => HypercubeRamsey.S04.clipped β γ n g j v) := by
    funext j
    exact hclip j
  have hsorted : HypercubeRamsey.S04.sortedCounts β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.sortedCounts β γ n g v := by
    unfold HypercubeRamsey.S04.sortedCounts
    rw [hfun]
  have hstep : ∀ ab,
      HypercubeRamsey.S04.searchStep β γ n g (HypercubeRamsey.cubeFlip v i) ab =
        HypercubeRamsey.S04.searchStep β γ n g v ab := by
    intro ab
    simp [HypercubeRamsey.S04.searchStep, HypercubeRamsey.S04.rankValue, hsorted]
  have hleaf : HypercubeRamsey.S04.searchLeaf β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.searchLeaf β γ n g v := by
    have hfold (L : List ℕ) (ab : ℕ × ℕ) :
        List.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g
          (HypercubeRamsey.cubeFlip v i) ab) ab L =
        List.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab L := by
      induction L generalizing ab with
      | nil => rfl
      | cons a L ih => simp [List.foldl_cons, hstep, ih]
    unfold HypercubeRamsey.S04.searchLeaf
    exact hfold _ _
  unfold HypercubeRamsey.S04.gadgetOut
  rw [hleaf]
  simp [hclip]

private theorem sum_eq_sum_fiber_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) (g : κ → ℝ) :
    (∑ i, g (f i)) =
      ∑ k, ((Finset.univ.filter fun i : ι => f i = k).card : ℝ) * g k := by
  classical
  calc
    (∑ i, g (f i)) = ∑ i, ∑ k, (if f i = k then g k else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
    _ = ∑ k, ∑ i, (if f i = k then g k else 0) := Finset.sum_comm
    _ = ∑ k, ((Finset.univ.filter fun i : ι => f i = k).card : ℝ) * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp [Finset.sum_const]

private theorem sum_fiber_card_eq_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → κ) :
    (∑ k, ((Finset.univ.filter fun i : ι => f i = k).card : ℝ)) =
      Fintype.card ι := by
  classical
  have h := sum_eq_sum_fiber_card f (fun _ => (1 : ℝ))
  simpa using h.symm

theorem weightedTag_tail {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : FinProb ι) (α : κ → ℝ) (B K : ℝ)
    (hαsum : ∑ k, α k = 1) (hα : ∀ k, 0 ≤ α k)
    (hwidth : 0 < ∑ k, (α k * B) ^ 2)
    (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ B)
    (hmean : P.expect f ≤ K) (hK : 0 < K) :
    (FinProb.pi (fun _ : κ => P)).pr
      (fun tag : κ → ι => 2 * K < ∑ k, α k * f (tag k)) ≤
        2 * Real.exp (-2 * K ^ 2 / ∑ k, (α k * B) ^ 2) := by
  classical
  let X : κ → ι → ℝ := fun k i => α k * f i
  have hX : ∀ k i, 0 ≤ X k i ∧ X k i ≤ α k * B := by
    intro k i
    constructor
    · exact mul_nonneg (hα k) (hf i).1
    · exact mul_le_mul_of_nonneg_left (hf i).2 (hα k)
  have hwidth' : 0 < ∑ k, (α k * B - 0) ^ 2 := by simpa using hwidth
  have htail := HypercubeRamsey.xChernoff (fun _ : κ => P) X
    (fun _ => 0) (fun k => α k * B) hX hwidth' K hK
  have hmean' : ∑ k, P.expect (X k) ≤ K := by
    calc
      (∑ k, P.expect (X k)) = (∑ k, α k) * P.expect f := by
        simp [X, FinProb.expect_smul, ← Finset.sum_mul]
      _ = P.expect f := by rw [hαsum, one_mul]
      _ ≤ K := hmean
  have hsub : ∀ tag : κ → ι, (2 * K < ∑ k, α k * f (tag k)) →
      K ≤ |(∑ k, X k (tag k)) - ∑ k, P.expect (X k)| := by
    intro tag htag
    have hdiff : K < (∑ k, X k (tag k)) - ∑ k, P.expect (X k) := by
      dsimp [X]
      have : ∑ k, P.expect (X k) ≤ K := hmean'
      linarith
    have hpos : 0 < (∑ k, X k (tag k)) - ∑ k, P.expect (X k) := by linarith
    rw [abs_of_pos hpos]
    linarith
  exact (HypercubeRamsey.S04.pr_mono (FinProb.pi (fun _ : κ => P)) hsub).trans (by simpa using htail)

private theorem pr_exists_le {ι Ω : Type*} [Fintype ι] [Fintype Ω]
    (P : FinProb Ω) (A : ι → Ω → Prop) :
    P.pr (fun ω => ∃ i, A i ω) ≤ ∑ i, P.pr (A i) := by
  classical
  have haux (s : Finset ι) :
      P.pr (fun ω => ∃ i ∈ s, A i ω) ≤ ∑ i ∈ s, P.pr (A i) := by
    induction s using Finset.induction_on with
    | empty => simp [FinProb.pr]
    | @insert a s ha ih =>
      have heq : (fun ω => ∃ i ∈ insert a s, A i ω) =
          (fun ω => A a ω ∨ ∃ i ∈ s, A i ω) := by
        funext ω
        simp [ha]
      rw [heq]
      calc
        P.pr (fun ω => A a ω ∨ ∃ i ∈ s, A i ω) ≤
            P.pr (A a) + P.pr (fun ω => ∃ i ∈ s, A i ω) := FinProb.pr_union P _ _
        _ ≤ P.pr (A a) + ∑ i ∈ s, P.pr (A i) := add_le_add le_rfl ih
        _ = ∑ i ∈ insert a s, P.pr (A i) := by rw [Finset.sum_insert ha]
  simpa using haux (Finset.univ : Finset ι)

private def trueCoordinatesEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (ι → Bool) ≃ Finset ι where
  toFun f := Finset.univ.filter fun i => f i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv s := by
    ext i
    simp

private theorem boolFunction_weight_card (ℓ k : ℕ) :
    (Finset.univ.filter fun f : Fin ℓ → Bool =>
      (trueCoordinatesEquiv f).card = k).card = Nat.choose ℓ k := by
  classical
  let e := trueCoordinatesEquiv (ι := Fin ℓ)
  let A : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f => (e f).card = k
  have himage : A.image e = Finset.univ.powersetCard k := by
    ext s
    constructor
    · intro hs
      rcases Finset.mem_image.mp hs with ⟨f, hf, rfl⟩
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hf).2⟩
    · intro hs
      rcases Finset.mem_powersetCard.mp hs with ⟨_, hsk⟩
      refine Finset.mem_image.mpr ⟨e.symm s, ?_, e.apply_symm_apply s⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e] using hsk⟩
  rw [← Finset.card_image_of_injective A e.injective, himage, Finset.card_powersetCard]
  simp

private def boolWeightIndex (ℓ : ℕ) (f : Fin ℓ → Bool) : Fin (ℓ + 1) :=
  ⟨(trueCoordinatesEquiv f).card,
    Nat.lt_succ_of_le (by
      simpa using Finset.card_le_univ (trueCoordinatesEquiv f))⟩

private theorem boolFunction_weight_set_card (ℓ : ℕ) (T : Finset (Fin (ℓ + 1))) :
    ((Finset.univ.filter fun f : Fin ℓ → Bool => boolWeightIndex ℓ f ∈ T).card : ℝ) =
      ∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) := by
  classical
  have hcard := Finset.sum_card_fiberwise_eq_card_filter
    (s := (Finset.univ : Finset (Fin ℓ → Bool))) (t := T) (g := boolWeightIndex ℓ)
  have hfib (k : Fin (ℓ + 1)) :
      (Finset.univ.filter fun f : Fin ℓ → Bool => boolWeightIndex ℓ f = k).card =
        Nat.choose ℓ k.val := by
    simpa [boolWeightIndex, Fin.ext_iff] using boolFunction_weight_card ℓ k.val
  calc
    ((Finset.univ.filter fun f : Fin ℓ → Bool => boolWeightIndex ℓ f ∈ T).card : ℝ) =
        ((∑ k ∈ T, (Finset.univ.filter fun f : Fin ℓ → Bool =>
          boolWeightIndex ℓ f = k).card : ℕ) : ℝ) := by exact_mod_cast hcard.symm
    _ = ∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact_mod_cast hfib k

private def blockAssignmentsEquiv {ι : Type*} {m ℓ : ℕ}
    (e : ι × Fin ℓ ≃ Fin m) : (Fin m → Bool) ≃ (ι → Fin ℓ → Bool) where
  toFun f i j := f (e (i, j))
  invFun x k := x (e.symm k).1 (e.symm k).2
  left_inv f := by
    funext k
    simp
  right_inv x := by
    funext i j
    simp

private theorem block_constraint_count {ι : Type*} [Fintype ι] {m ℓ : ℕ}
    (e : ι × Fin ℓ ≃ Fin m) (A : ι → Finset (Fin ℓ → Bool)) :
    Fintype.card {f : Fin m → Bool // ∀ i, (blockAssignmentsEquiv e f) i ∈ A i} =
      ∏ i, (A i).card := by
  classical
  let E := blockAssignmentsEquiv e
  let P := Fintype.piFinset A
  let F : {f : Fin m → Bool // ∀ i, (E f) i ∈ A i} ≃ {x : ι → Fin ℓ → Bool // x ∈ P} := {
    toFun := fun f => ⟨E f.1, Fintype.mem_piFinset.mpr f.2⟩
    invFun := fun x => ⟨E.symm x.1, by
      intro i
      simpa [E] using Fintype.mem_piFinset.mp x.2 i⟩
    left_inv := by intro f; apply Subtype.ext; simp [E]
    right_inv := by intro x; apply Subtype.ext; simp [E]
  }
  calc
    Fintype.card {f : Fin m → Bool // ∀ i, (blockAssignmentsEquiv e f) i ∈ A i} =
        Fintype.card {x : ι → Fin ℓ → Bool // x ∈ P} := by
          apply Fintype.card_congr F
    _ = P.card := by exact Fintype.card_coe P
    _ = ∏ i, (A i).card := by simp [P, Fintype.card_piFinset]

private theorem block_constraint_fraction {ι : Type*} [Fintype ι] {m ℓ : ℕ}
    (e : ι × Fin ℓ ≃ Fin m) (A : ι → Finset (Fin ℓ → Bool))
    (hA : ∀ i, ((A i).card : ℝ) ≤ (2 / 3) * (2 : ℝ) ^ ℓ) :
    (Fintype.card {f : Fin m → Bool // ∀ i, (blockAssignmentsEquiv e f) i ∈ A i} : ℝ) ≤
      (2 / 3) ^ Fintype.card ι * (2 : ℝ) ^ m := by
  classical
  have hdim : Fintype.card ι * ℓ = m := by
    have h := Fintype.card_congr e
    simpa using h
  rw [block_constraint_count]
  rw [Nat.cast_prod]
  calc
    (∏ i, ((A i).card : ℝ)) ≤ ∏ i : ι, ((2 / 3 : ℝ) * (2 : ℝ) ^ ℓ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Nat.cast_nonneg _
      · intro i hi
        exact hA i
    _ = (2 / 3) ^ Fintype.card ι * (2 : ℝ) ^ m := by
      calc
        ∏ i : ι, ((2 / 3 : ℝ) * (2 : ℝ) ^ ℓ) =
            (∏ i : ι, (2 / 3 : ℝ)) * ∏ i : ι, (2 : ℝ) ^ ℓ := Finset.prod_mul_distrib
        _ = (2 / 3) ^ Fintype.card ι * (2 : ℝ) ^ (ℓ * Fintype.card ι) := by
          simp only [Finset.prod_const, Finset.card_univ]
          rw [pow_mul]
        _ = (2 / 3) ^ Fintype.card ι * (2 : ℝ) ^ m := by
          have hdim' : ℓ * Fintype.card ι = m := by rw [mul_comm, hdim]
          rw [hdim']

private theorem searchStep_interval {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ HypercubeRamsey.S04.gadgetPower β γ n) :
    (HypercubeRamsey.S04.searchStep β γ n g v (a, b)).1 ≤
      (HypercubeRamsey.S04.searchStep β γ n g v (a, b)).2 ∧
    (HypercubeRamsey.S04.searchStep β γ n g v (a, b)).2 ≤
      HypercubeRamsey.S04.gadgetPower β γ n := by
  have hmidlo : a ≤ (a + b) / 2 := by omega
  have hmidhi : (a + b) / 2 ≤ b := by omega
  unfold HypercubeRamsey.S04.searchStep
  split_ifs
  · exact ⟨hmidlo, hmidhi.trans hb⟩
  · exact ⟨hmidhi, hb⟩

private theorem searchFold_interval {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) :
    ∀ (L : List ℕ) (ab : ℕ × ℕ), ab.1 ≤ ab.2 →
      ab.2 ≤ HypercubeRamsey.S04.gadgetPower β γ n →
      (L.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab).1 ≤
          (L.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab).2 ∧
        (L.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab).2 ≤
          HypercubeRamsey.S04.gadgetPower β γ n := by
  intro L
  induction L with
  | nil => intro ab hab hb; simpa using And.intro hab hb
  | cons x L ih =>
      intro ab hab hb
      simp only [List.foldl_cons]
      have hs := searchStep_interval g v ab.1 ab.2 hab hb
      exact ih _ hs.1 hs.2

private theorem searchStep_first_lt_power {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n)
    (a b : ℕ) (hab : a ≤ b) (ha : a < HypercubeRamsey.S04.gadgetPower β γ n)
    (hb : b ≤ HypercubeRamsey.S04.gadgetPower β γ n) :
    (HypercubeRamsey.S04.searchStep β γ n g v (a, b)).1 <
        HypercubeRamsey.S04.gadgetPower β γ n ∧
      (HypercubeRamsey.S04.searchStep β γ n g v (a, b)).2 ≤
        HypercubeRamsey.S04.gadgetPower β γ n := by
  have hmidlt : (a + b) / 2 < HypercubeRamsey.S04.gadgetPower β γ n := by omega
  have hmidle : (a + b) / 2 ≤ b := by omega
  unfold HypercubeRamsey.S04.searchStep
  split_ifs
  · exact ⟨ha, hmidle.trans hb⟩
  · exact ⟨hmidlt, hb⟩

private theorem searchFold_first_lt_power {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) :
    ∀ (L : List ℕ) (ab : ℕ × ℕ), ab.1 ≤ ab.2 →
      ab.1 < HypercubeRamsey.S04.gadgetPower β γ n →
      ab.2 ≤ HypercubeRamsey.S04.gadgetPower β γ n →
      (L.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab).1 <
          HypercubeRamsey.S04.gadgetPower β γ n ∧
        (L.foldl (fun ab _ => HypercubeRamsey.S04.searchStep β γ n g v ab) ab).2 ≤
          HypercubeRamsey.S04.gadgetPower β γ n := by
  intro L
  induction L with
  | nil => intro ab hab ha hb; simpa using And.intro ha hb
  | cons x L ih =>
      intro ab hab ha hb
      simp only [List.foldl_cons]
      have hs := searchStep_interval g v ab.1 ab.2 hab hb
      have hlt := searchStep_first_lt_power g v ab.1 ab.2 hab ha hb
      exact ih _ hs.1 hlt.1 hs.2

private theorem searchLeaf_first_lt_power {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) :
    (HypercubeRamsey.S04.searchLeaf β γ n g v).1 < HypercubeRamsey.S04.gadgetPower β γ n := by
  have h := searchFold_first_lt_power g v
    (List.range (Nat.log2 (HypercubeRamsey.S04.gadgetPower β γ n)))
    (0, HypercubeRamsey.S04.gadgetPower β γ n) (by omega)
    (HypercubeRamsey.S04.gadgetPower_pos β γ n) le_rfl
  simpa [HypercubeRamsey.S04.searchLeaf] using h.1

private def gadgetChunkEquiv (G s ℓ : ℕ) :
    (Fin G × Fin s) × Fin ℓ ≃ Fin (G * s * ℓ) :=
  (Equiv.prodCongr (finProdFinEquiv : Fin G × Fin s ≃ Fin (G * s))
    (Equiv.refl (Fin ℓ))).trans
    (finProdFinEquiv : Fin (G * s) × Fin ℓ ≃ Fin ((G * s) * ℓ))

private theorem gadgetChunkEquiv_val {G s ℓ : ℕ}
    (g : Fin G) (j : Fin s) (r : Fin ℓ) :
    (gadgetChunkEquiv G s ℓ ((g, j), r)).val = (g.val * s + j.val) * ℓ + r.val := by
  simp [gadgetChunkEquiv, finProdFinEquiv]
  ring

private theorem chunkEnd_le_specialNum {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)) :
    HypercubeRamsey.S04.chunkStart β γ n g j +
      HypercubeRamsey.S04.chunkLen β γ n ≤ HypercubeRamsey.S04.specialNum β γ n := by
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hgs : g.val * s + j.val + 1 ≤ (g.val + 1) * s := by
    rw [Nat.add_mul, one_mul]
    omega
  have hG : (g.val + 1) * s ≤ G * s :=
    Nat.mul_le_mul_right s (Nat.succ_le_of_lt g.isLt)
  have hblock : (g.val * s + j.val) * ℓ + ℓ ≤ G * s * ℓ := by
    calc
      (g.val * s + j.val) * ℓ + ℓ = (g.val * s + j.val + 1) * ℓ := by
        ring
      _ ≤ ((g.val + 1) * s) * ℓ := Nat.mul_le_mul_right ℓ hgs
      _ ≤ (G * s) * ℓ := Nat.mul_le_mul_right ℓ hG
      _ = G * s * ℓ := by ring
  simpa [HypercubeRamsey.S04.chunkStart, HypercubeRamsey.S04.chunkLen,
    HypercubeRamsey.S04.specialNum, G, s, ℓ] using hblock

private theorem chunkCount_eq_blockWeight {β γ : ℝ} {n : ℕ}
    (hmn : HypercubeRamsey.S04.specialNum β γ n ≤ n)
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)) (v : CubeVertex n) :
    HypercubeRamsey.S04.chunkCount β γ n g j v =
      (Finset.univ.filter (fun r : Fin (HypercubeRamsey.S04.chunkLen β γ n) =>
        v (Fin.castLE
          (by simpa [HypercubeRamsey.S04.specialNum, Nat.mul_assoc] using hmn)
          (gadgetChunkEquiv (HypercubeRamsey.S04.gadgetNum β γ n)
            (HypercubeRamsey.S04.chunkNum β γ n)
            (HypercubeRamsey.S04.chunkLen β γ n) ((g, j), r))) = true)).card := by
  classical
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hmn' : G * s * ℓ ≤ n := by
    simpa [HypercubeRamsey.S04.specialNum, G, s, ℓ, Nat.mul_assoc] using hmn
  let φ : Fin ℓ → Fin n := fun r => Fin.castLE hmn' (gadgetChunkEquiv G s ℓ ((g, j), r))
  have hφval (r : Fin ℓ) :
      (φ r).val = (g.val * s + j.val) * ℓ + r.val := by
    simpa [φ, G, s, ℓ] using gadgetChunkEquiv_val g j r
  have hStartVal : HypercubeRamsey.S04.chunkStart β γ n g j =
      (g.val * s + j.val) * ℓ := by simp [HypercubeRamsey.S04.chunkStart, G, s, ℓ]
  have himage :
      HypercubeRamsey.S04.chunkCoords β γ n g j =
        (Finset.univ : Finset (Fin ℓ)).image φ := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨_, ⟨hstart, hend⟩⟩
      let r : Fin ℓ := ⟨i.val - HypercubeRamsey.S04.chunkStart β γ n g j, by
        have hstart' : HypercubeRamsey.S04.chunkStart β γ n g j ≤ i.val := hstart
        have hend' : i.val <
            HypercubeRamsey.S04.chunkStart β γ n g j + HypercubeRamsey.S04.chunkLen β γ n := hend
        exact (Nat.sub_lt_iff_lt_add hstart').2 (by omega)⟩
      refine Finset.mem_image.mpr ⟨r, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rw [hφval]
      have hrval : r.val = i.val - HypercubeRamsey.S04.chunkStart β γ n g j := rfl
      rw [hrval, ← hStartVal]
      omega
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨r, _, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [HypercubeRamsey.S04.chunkStart, hφval]
      dsimp [s, ℓ]
      constructor <;> omega
  have hφinj : Function.Injective φ := by
    intro r r' h
    apply Fin.ext
    have hv := congrArg Fin.val h
    rw [hφval r, hφval r'] at hv
    omega
  have hfilter :
      (HypercubeRamsey.S04.chunkCoords β γ n g j).filter (fun i => v i = true) =
        (Finset.univ.filter fun r : Fin ℓ => v (φ r) = true).image φ := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨hiCoord, hbit⟩
      rw [himage] at hiCoord
      rcases Finset.mem_image.mp hiCoord with ⟨r, _, hr⟩
      refine Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hr⟩
      simpa [hr] using hbit
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨r, hr, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, (Finset.mem_filter.mp hr).2⟩
      rw [himage]
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  unfold HypercubeRamsey.S04.chunkCount
  rw [hfilter, Finset.card_image_of_injective _ hφinj]

private theorem odd_parity_projection_uniform {n : ℕ} (S : Finset (Fin n))
    (hS : S.card < n) (z : ∀ i : S, Bool) :
    ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
      (fun v : CubeVertex n => ∀ i : S, v i.1 = z i)).card = 2 ^ (n - S.card - 1) := by
  classical
  let agree : CubeVertex n → Prop := fun v => ∀ i : S, v i.1 = z i
  let evenF : Finset (CubeVertex n) := (HypercubeRamsey.evenRoleSet n).filter agree
  let oddF : Finset (CubeVertex n) := (Finset.univ \ HypercubeRamsey.evenRoleSet n).filter agree
  obtain ⟨j, hjU, hjS⟩ := Finset.exists_mem_notMem_of_card_lt_card (by
    simpa using hS : S.card < (Finset.univ : Finset (Fin n)).card)
  let flip : CubeVertex n → CubeVertex n := fun v => HypercubeRamsey.cubeFlip v j
  have hinv : Function.Involutive flip := by
    intro v
    funext i
    by_cases hji : i = j
    · subst i
      simp [flip, HypercubeRamsey.cubeFlip]
    · simp [flip, HypercubeRamsey.cubeFlip, hji]
  have hpres (v : CubeVertex n) : agree (flip v) ↔ agree v := by
    constructor <;> intro h i
    · have hne : i.1 ≠ j := by
        intro hEq
        exact hjS (hEq ▸ i.2)
      simpa [agree, flip, HypercubeRamsey.cubeFlip, Function.update_of_ne hne] using h i
    · have hne : i.1 ≠ j := by
        intro hEq
        exact hjS (hEq ▸ i.2)
      simpa [agree, flip, HypercubeRamsey.cubeFlip, Function.update_of_ne hne] using h i
  have himage : evenF.image flip = oddF := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      have hxE : HypercubeRamsey.IsEvenRole x := by
        simpa [HypercubeRamsey.evenRoleSet] using (Finset.mem_filter.mp hx).1
      have hnot : ¬ HypercubeRamsey.IsEvenRole (flip x) := by
        intro hflip
        exact (HypercubeRamsey.cubeFlip_parity x j).mp hflip hxE
      have hagr : agree (flip x) := (hpres x).2 (Finset.mem_filter.mp hx).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩, hagr⟩
      simpa [HypercubeRamsey.evenRoleSet] using hnot
    · intro hy
      have hodd : ¬ HypercubeRamsey.IsEvenRole y := by
        simpa [HypercubeRamsey.evenRoleSet] using (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
      have hagr : agree y := (Finset.mem_filter.mp hy).2
      have hE : HypercubeRamsey.IsEvenRole (flip y) :=
        (HypercubeRamsey.cubeFlip_parity y j).mpr hodd
      refine Finset.mem_image.mpr ⟨flip y, ?_, hinv y⟩
      have hagr' : agree (flip y) := (hpres y).mpr hagr
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩, hagr'⟩
  have hcard : evenF.card = oddF.card := by
    rw [← Finset.card_image_of_injective evenF hinv.injective, himage]
  have he := HypercubeRamsey.parity_projection_uniform S hS z
  calc
    oddF.card = evenF.card := hcard.symm
    _ = 2 ^ (n - S.card - 1) := by simpa [evenF, agree] using he

theorem evenProjection_event_card {n : ℕ} (S : Finset (Fin n))
    (hS : S.card < n) (A : Finset (∀ i : S, Bool)) :
    ((HypercubeRamsey.evenRoleSet n).filter
      (fun v : CubeVertex n => (fun i : S => v i.1) ∈ A)).card =
        A.card * 2 ^ (n - S.card - 1) := by
  classical
  let project : CubeVertex n → (∀ i : S, Bool) := fun v i => v i.1
  have hcard := Finset.sum_card_fiberwise_eq_card_filter
    (s := HypercubeRamsey.evenRoleSet n) (t := A) (g := project)
  have hfiber (z : ∀ i : S, Bool) :
      ((HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n => project v = z).card =
        2 ^ (n - S.card - 1) := by
    have hEq : (HypercubeRamsey.evenRoleSet n).filter
          (fun v : CubeVertex n => project v = z) =
        (HypercubeRamsey.evenRoleSet n).filter
          (fun v => ∀ i : S, v i.1 = z i) := by
      ext v
      simp [project, funext_iff]
    rw [hEq]
    exact HypercubeRamsey.parity_projection_uniform S hS z
  calc
    ((HypercubeRamsey.evenRoleSet n).filter
      (fun v : CubeVertex n => project v ∈ A)).card =
        ∑ z ∈ A, ((HypercubeRamsey.evenRoleSet n).filter
          (fun v : CubeVertex n => project v = z)).card := hcard.symm
    _ = ∑ _z ∈ A, 2 ^ (n - S.card - 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hfiber z
    _ = A.card * 2 ^ (n - S.card - 1) := by simp

theorem oddProjection_event_card {n : ℕ} (S : Finset (Fin n))
    (hS : S.card < n) (A : Finset (∀ i : S, Bool)) :
    ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
      (fun v : CubeVertex n => (fun i : S => v i.1) ∈ A)).card =
        A.card * 2 ^ (n - S.card - 1) := by
  classical
  let project : CubeVertex n → (∀ i : S, Bool) := fun v i => v i.1
  have hcard := Finset.sum_card_fiberwise_eq_card_filter
    (s := Finset.univ \ HypercubeRamsey.evenRoleSet n) (t := A) (g := project)
  have hfiber (z : ∀ i : S, Bool) :
      ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
        (fun v : CubeVertex n => project v = z)).card =
        2 ^ (n - S.card - 1) := by
    have hEq : (Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
          (fun v : CubeVertex n => project v = z) =
        (Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
          (fun v => ∀ i : S, v i.1 = z i) := by
      ext v
      simp [project, funext_iff]
    rw [hEq]
    exact odd_parity_projection_uniform S hS z
  calc
    ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
      (fun v : CubeVertex n => project v ∈ A)).card =
        ∑ z ∈ A, ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter
          (fun v : CubeVertex n => project v = z)).card := hcard.symm
    _ = ∑ _z ∈ A, 2 ^ (n - S.card - 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hfiber z
    _ = A.card * 2 ^ (n - S.card - 1) := by simp

def firstCoordinates (n m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < m

def firstCoordinatesEquiv {m n : ℕ} (hm : m ≤ n) :
    Fin m ≃ {i : Fin n // i ∈ firstCoordinates n m} where
  toFun i := ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩, by
    simp [firstCoordinates, i.isLt]⟩
  invFun i := ⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩
  left_inv i := by apply Fin.ext; rfl
  right_inv i := by apply Subtype.ext; apply Fin.ext; rfl

private def firstAssignmentEquiv {m n : ℕ} (hm : m ≤ n) :
    (Fin m → Bool) ≃ (∀ i : {x : Fin n // x ∈ firstCoordinates n m}, Bool) where
  toFun f i := f ((firstCoordinatesEquiv hm).symm i)
  invFun z j := z (firstCoordinatesEquiv hm j)
  left_inv f := by funext j; simp
  right_inv z := by funext i; simp

def gadgetFirstBlocksEquiv {G s ℓ n : ℕ} (hmn : G * s * ℓ ≤ n) :
    (∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool) ≃
      (Fin G × Fin s → Fin ℓ → Bool) :=
  (firstAssignmentEquiv (m := G * s * ℓ) (n := n) hmn).symm.trans
    (blockAssignmentsEquiv (gadgetChunkEquiv G s ℓ))

private theorem gadgetFirstBlock_constraint_count {G s ℓ n : ℕ}
    (hmn : G * s * ℓ ≤ n) (A : (Fin G × Fin s) → Finset (Fin ℓ → Bool)) :
    Fintype.card
      {z : (∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool) //
        ∀ b, (gadgetFirstBlocksEquiv hmn z) b ∈ A b} =
      ∏ b, (A b).card := by
  classical
  let E := gadgetFirstBlocksEquiv hmn
  let Eblock := blockAssignmentsEquiv (gadgetChunkEquiv G s ℓ)
  let Q : (Fin G × Fin s → Fin ℓ → Bool) → Prop := fun x => ∀ b, x b ∈ A b
  let R : (Fin (G * s * ℓ) → Bool) → Prop := fun f => ∀ b, (Eblock f) b ∈ A b
  let eS : {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool //
      Q (E z)} ≃ {x : Fin G × Fin s → Fin ℓ → Bool // Q x} := {
    toFun := fun z => ⟨E z.1, z.2⟩
    invFun := fun x => ⟨E.symm x.1, by simpa [E, Q] using x.2⟩
    left_inv := by intro z; apply Subtype.ext; simp [E]
    right_inv := by intro x; apply Subtype.ext; simp [E]
  }
  let eSub : {x : Fin G × Fin s → Fin ℓ → Bool // Q x} ≃
      {f : Fin (G * s * ℓ) → Bool // R f} := {
    toFun := fun x => ⟨Eblock.symm x.1, by
      intro b
      simpa [Eblock] using x.2 b⟩
    invFun := fun f => ⟨Eblock f.1, f.2⟩
    left_inv := by intro x; apply Subtype.ext; simp [Eblock]
    right_inv := by intro f; apply Subtype.ext; simp [Eblock]
  }
  calc
    Fintype.card {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool //
      Q (E z)} = Fintype.card {x : Fin G × Fin s → Fin ℓ → Bool // Q x} := by
        exact Fintype.card_congr eS
    _ = Fintype.card {f : Fin (G * s * ℓ) → Bool // R f} :=
        Fintype.card_congr eSub
    _ = ∏ b, (A b).card := by
      simpa [R, Eblock, blockAssignmentsEquiv] using
        block_constraint_count (gadgetChunkEquiv G s ℓ) A

private theorem gadgetFirstBlocks_apply {G s ℓ n : ℕ} (hmn : G * s * ℓ ≤ n)
    (v : CubeVertex n) (g : Fin G) (j : Fin s) (r : Fin ℓ) :
    (gadgetFirstBlocksEquiv hmn (fun i => v i.1) (g, j)) r =
      v (Fin.castLE hmn (gadgetChunkEquiv G s ℓ ((g, j), r))) := by
  calc
    (gadgetFirstBlocksEquiv hmn (fun i => v i.1) (g, j)) r =
        v ((firstCoordinatesEquiv hmn (gadgetChunkEquiv G s ℓ ((g, j), r))).1) := by
          simp [gadgetFirstBlocksEquiv, firstAssignmentEquiv, blockAssignmentsEquiv]
    _ = v (Fin.castLE hmn (gadgetChunkEquiv G s ℓ ((g, j), r))) := by
      congr 1

private theorem key_output_side_constraint {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n) (v : CubeVertex n)
    (hkey : HypercubeRamsey.S04.key β γ n v = κ)
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)) :
    (j ∈ (κ g).2 →
      (HypercubeRamsey.S04.searchLeaf β γ n g v).1 *
          HypercubeRamsey.S04.gadgetPower β γ n +
          HypercubeRamsey.S04.gadgetPower β γ n / 2 <
        HypercubeRamsey.S04.clipped β γ n g j v) ∧
    (j ∉ (κ g).2 →
      HypercubeRamsey.S04.clipped β γ n g j v ≤
        (HypercubeRamsey.S04.searchLeaf β γ n g v).1 *
          HypercubeRamsey.S04.gadgetPower β γ n +
          HypercubeRamsey.S04.gadgetPower β γ n / 2) := by
  have hGout : HypercubeRamsey.S04.gadgetOut β γ n g v = κ g := by
    have h := congrFun hkey g
    simpa [HypercubeRamsey.S04.key] using h
  have hsnd := congrArg Prod.snd hGout
  have hiff : j ∈ (κ g).2 ↔
      (HypercubeRamsey.S04.searchLeaf β γ n g v).1 *
          HypercubeRamsey.S04.gadgetPower β γ n +
          HypercubeRamsey.S04.gadgetPower β γ n / 2 <
        HypercubeRamsey.S04.clipped β γ n g j v := by
    rw [← hsnd]
    simp [HypercubeRamsey.S04.gadgetOut]
  constructor
  · exact hiff.mp
  · intro hj
    by_contra hn
    exact hj (hiff.mpr (lt_of_not_ge hn))

private def boolComplementEquiv (ℓ : ℕ) : (Fin ℓ → Bool) ≃ (Fin ℓ → Bool) where
  toFun f := fun i => !f i
  invFun f := fun i => !f i
  left_inv f := by funext i; cases h : f i <;> simp [h]
  right_inv f := by funext i; cases h : f i <;> simp [h]

private theorem boolWeight_complement (ℓ : ℕ) (f : Fin ℓ → Bool) :
    (trueCoordinatesEquiv ((boolComplementEquiv ℓ) f)).card =
      ℓ - (trueCoordinatesEquiv f).card := by
  classical
  have hset : trueCoordinatesEquiv ((boolComplementEquiv ℓ) f) =
      (Finset.univ : Finset (Fin ℓ)) \ trueCoordinatesEquiv f := by
    ext i
    simp [boolComplementEquiv, trueCoordinatesEquiv]
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

private theorem weight_interval_card_le (ℓ lo hi W : ℕ) (hhi : hi ≤ lo + W) :
    (Finset.univ.filter fun k : Fin (ℓ + 1) => lo < k.val ∧ k.val < hi).card ≤ W + 2 := by
  classical
  let I := Finset.univ.filter fun k : Fin (ℓ + 1) => lo < k.val ∧ k.val < hi
  let f : {k : Fin (ℓ + 1) // k ∈ I} → Fin (W + 2) := fun k =>
    ⟨k.1.val - lo, by
      have hk := (Finset.mem_filter.mp k.2).2
      omega⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    have hv : a.1.val - lo = b.1.val - lo := congrArg Fin.val h
    have ha : lo ≤ a.1.val := (Finset.mem_filter.mp a.2).2.1.le
    have hb : lo ≤ b.1.val := (Finset.mem_filter.mp b.2).2.1.le
    exact (tsub_left_inj ha hb).mp hv
  have hc := Fintype.card_le_of_injective f hinj
  calc
    I.card = Fintype.card {k : Fin (ℓ + 1) // k ∈ I} := (Fintype.card_coe I).symm
    _ ≤ Fintype.card (Fin (W + 2)) := hc
    _ = W + 2 := Fintype.card_fin _

private theorem centralWeightMass_le_sixth (S ℓ : ℕ) (hS : 100 ≤ S)
    (hℓ : ℓ = (S - 1) ^ 6) :
    ∑ k ∈ (Finset.univ.filter fun k : Fin (ℓ + 1) =>
      ℓ / 2 - S ^ 2 / 2 < k.val ∧
        k.val < (ℓ / 2 - S ^ 2 / 2) + S ^ 2),
      (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ ≤ 1 / 6 := by
  classical
  let s := S - 1
  let lo := ℓ / 2 - S ^ 2 / 2
  let hi := lo + S ^ 2
  let T : Finset (Fin (ℓ + 1)) := Finset.univ.filter fun k => lo < k.val ∧ k.val < hi
  have hsNat : 99 ≤ s := by dsimp [s]; omega
  have hsReal : 99 ≤ (s : ℝ) := by exact_mod_cast hsNat
  have hellNat : 0 < ℓ := by rw [hℓ]; positivity
  have hellReal : (ℓ : ℝ) = (s : ℝ) ^ 6 := by
    dsimp [s]
    rw [hℓ]
    norm_cast
  have hsqrt : Real.sqrt (ℓ : ℝ) = (s : ℝ) ^ 3 := by
    rw [hellReal, show (s : ℝ) ^ 6 = ((s : ℝ) ^ 3) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hTcard : T.card ≤ S ^ 2 + 2 := by
    apply weight_interval_card_le ℓ lo hi (S ^ 2)
    rfl
  have hEllPos : (0 : ℝ) < ℓ := by exact_mod_cast hellNat
  have hAtom (k : Fin (ℓ + 1)) :
      (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ ≤ 2 / Real.sqrt (ℓ : ℝ) :=
    HypercubeRamsey.centralBinomialUpper ℓ hellNat k.val (Nat.le_of_lt_succ k.isLt)
  have hmass :
      (∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ) ≤
        (T.card : ℝ) * (2 / Real.sqrt (ℓ : ℝ)) := by
    calc
      (∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ) ≤
          ∑ _k ∈ T, 2 / Real.sqrt (ℓ : ℝ) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hAtom k
      _ = (T.card : ℝ) * (2 / Real.sqrt (ℓ : ℝ)) := by simp
  have hSleNat : S ≤ 2 * (S - 1) := by omega
  have hSle : (S : ℝ) ≤ 2 * (s : ℝ) := by
    dsimp [s]
    exact_mod_cast hSleNat
  have hsq : (S : ℝ) ^ 2 ≤ (2 * (s : ℝ)) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hSle
  have hsSqOne : 1 ≤ (s : ℝ) ^ 2 := by nlinarith [sq_nonneg ((s : ℝ) - 1)]
  have hSsq : (S : ℝ) ^ 2 + 2 ≤ 6 * (s : ℝ) ^ 2 := by nlinarith [hsq, hsSqOne]
  have hs72 : 72 ≤ (s : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_right hs72 (sq_nonneg (s : ℝ))
  have hcoef : 12 * ((S : ℝ) ^ 2 + 2) ≤ (s : ℝ) ^ 3 := by nlinarith [hSsq, hprod]
  have hsmall : ((S ^ 2 + 2 : ℕ) : ℝ) * (2 / (s : ℝ) ^ 3) ≤ 1 / 6 := by
    have heq : ((S ^ 2 + 2 : ℕ) : ℝ) * (2 / (s : ℝ) ^ 3) =
        2 * ((S : ℝ) ^ 2 + 2) / (s : ℝ) ^ 3 := by push_cast; ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (s : ℝ) ^ 3)).2
    nlinarith [hcoef]
  calc
    (∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ) ≤
        (T.card : ℝ) * (2 / Real.sqrt (ℓ : ℝ)) := hmass
    _ ≤ ((S ^ 2 + 2 : ℕ) : ℝ) * (2 / Real.sqrt (ℓ : ℝ)) := by
      gcongr
    _ = ((S ^ 2 + 2 : ℕ) : ℝ) * (2 / (s : ℝ) ^ 3) := by rw [hsqrt]
    _ ≤ 1 / 6 := hsmall

def clippedBlockWeight (S ℓ : ℕ) (f : Fin ℓ → Bool) : ℕ :=
  min ((trueCoordinatesEquiv f).card - (ℓ / 2 - S ^ 2 / 2)) (S ^ 2)

private theorem clippedBlock_side_card_le (S ℓ t : ℕ)
    (hendLow : ((Finset.univ.filter fun f : Fin ℓ → Bool =>
      (trueCoordinatesEquiv f).card ≤ ℓ / 2 - S ^ 2 / 2).card : ℝ) ≥
        (1 / 3) * (2 : ℝ) ^ ℓ)
    (hendHigh : ((Finset.univ.filter fun f : Fin ℓ → Bool =>
      ℓ / 2 - S ^ 2 / 2 + S ^ 2 ≤ (trueCoordinatesEquiv f).card).card : ℝ) ≥
        (1 / 3) * (2 : ℝ) ^ ℓ)
    (htpos : 0 < t) (htlt : t < S ^ 2) :
    ((Finset.univ.filter fun f : Fin ℓ → Bool => t < clippedBlockWeight S ℓ f).card : ℝ) ≤
        (2 / 3) * (2 : ℝ) ^ ℓ ∧
    ((Finset.univ.filter fun f : Fin ℓ → Bool => clippedBlockWeight S ℓ f ≤ t).card : ℝ) ≤
        (2 / 3) * (2 : ℝ) ^ ℓ := by
  classical
  let lo := ℓ / 2 - S ^ 2 / 2
  let hi := lo + S ^ 2
  let lowW : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f =>
    (trueCoordinatesEquiv f).card ≤ lo
  let highW : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f =>
    hi ≤ (trueCoordinatesEquiv f).card
  let above : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f =>
    t < clippedBlockWeight S ℓ f
  let below : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f =>
    clippedBlockWeight S ℓ f ≤ t
  have hlowW : (lowW.card : ℝ) ≥ (1 / 3) * (2 : ℝ) ^ ℓ := by
    simpa [lowW, lo] using hendLow
  have hhighW : (highW.card : ℝ) ≥ (1 / 3) * (2 : ℝ) ^ ℓ := by
    simpa [highW, lo, hi] using hendHigh
  have hlowClip (f : Fin ℓ → Bool) (hf : f ∈ lowW) : clippedBlockWeight S ℓ f = 0 := by
    have hw := (Finset.mem_filter.mp hf).2
    simp [clippedBlockWeight, lo, Nat.sub_eq_zero_of_le hw]
  have hhighClip (f : Fin ℓ → Bool) (hf : f ∈ highW) :
      clippedBlockWeight S ℓ f = S ^ 2 := by
    have hw := (Finset.mem_filter.mp hf).2
    have hsub : S ^ 2 ≤ (trueCoordinatesEquiv f).card - lo := by dsimp [lo] at hw ⊢; omega
    simp [clippedBlockWeight, lo, Nat.min_eq_right hsub]
  have hlowNotAbove : lowW ⊆ Finset.univ.filter fun f : Fin ℓ → Bool => ¬ t < clippedBlockWeight S ℓ f := by
    intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hlowClip f hf]
    omega
  have hhighNotBelow : highW ⊆ Finset.univ.filter fun f : Fin ℓ → Bool => ¬ clippedBlockWeight S ℓ f ≤ t := by
    intro f hf
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hhighClip f hf]
    omega
  have htotal : (Finset.univ : Finset (Fin ℓ → Bool)).card = 2 ^ ℓ := by simp
  have hsplitAbove := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin ℓ → Bool)))
    (p := fun f => t < clippedBlockWeight S ℓ f)
  have hsplitBelow := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin ℓ → Bool)))
    (p := fun f => clippedBlockWeight S ℓ f ≤ t)
  have hAboveNat : above.card + lowW.card ≤ 2 ^ ℓ := by
    have hle := Finset.card_le_card hlowNotAbove
    dsimp [above]
    omega
  have hBelowNat : below.card + highW.card ≤ 2 ^ ℓ := by
    have hle := Finset.card_le_card hhighNotBelow
    dsimp [below]
    omega
  constructor
  · have hsmall : (above.card : ℝ) + (lowW.card : ℝ) ≤ (2 : ℝ) ^ ℓ := by exact_mod_cast hAboveNat
    nlinarith [hlowW, hsmall]
  · have hsmall : (below.card : ℝ) + (highW.card : ℝ) ≤ (2 : ℝ) ^ ℓ := by exact_mod_cast hBelowNat
    nlinarith [hhighW, hsmall]

private theorem clipped_endpoint_counts (S ℓ : ℕ) (hS : 100 ≤ S)
    (hSeven : Even S) (hℓ : ℓ = (S - 1) ^ 6) :
    ((Finset.univ.filter fun f : Fin ℓ → Bool =>
      (trueCoordinatesEquiv f).card ≤ ℓ / 2 - S ^ 2 / 2).card : ℝ) ≥
        (1 / 3) * (2 : ℝ) ^ ℓ ∧
    ((Finset.univ.filter fun f : Fin ℓ → Bool =>
      ℓ / 2 - S ^ 2 / 2 + S ^ 2 ≤ (trueCoordinatesEquiv f).card).card : ℝ) ≥
        (1 / 3) * (2 : ℝ) ^ ℓ := by
  classical
  let w : (Fin ℓ → Bool) → ℕ := fun f => (trueCoordinatesEquiv f).card
  let lo := ℓ / 2 - S ^ 2 / 2
  let hi := lo + S ^ 2
  let low : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f => w f ≤ lo
  let mid : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f => lo < w f ∧ w f < hi
  let high : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f => hi ≤ w f
  let boundary : Finset (Fin ℓ → Bool) := Finset.univ.filter fun f => w f = lo + 1
  let T : Finset (Fin (ℓ + 1)) := Finset.univ.filter fun k => lo < k.val ∧ k.val < hi
  rcases hSeven with ⟨t, ht⟩
  have hSsq : S ^ 2 = 2 * (S ^ 2 / 2) := by
    have h : S ^ 2 = 4 * t ^ 2 := by rw [ht]; ring
    rw [h]
    omega
  have hs : 99 ≤ S - 1 := by omega
  have hS_le_2s : S ≤ 2 * (S - 1) := by omega
  have hsSq : 2 ≤ (S - 1) ^ 2 := by nlinarith [hS]
  have h2s_le_s3 : 2 * (S - 1) ≤ (S - 1) ^ 3 := by
    calc
      2 * (S - 1) ≤ (S - 1) ^ 2 * (S - 1) := Nat.mul_le_mul_right _ hsSq
      _ = (S - 1) ^ 3 := by ring
  have hS_le_s3 : S ≤ (S - 1) ^ 3 := hS_le_2s.trans h2s_le_s3
  have hSsqLeEll : S ^ 2 ≤ ℓ := by
    calc
      S ^ 2 ≤ ((S - 1) ^ 3) ^ 2 := Nat.pow_le_pow_left hS_le_s3 2
      _ = (S - 1) ^ 6 := by rw [← Nat.pow_mul]
      _ = ℓ := hℓ.symm
  have hClipHalf : S ^ 2 / 2 ≤ ℓ / 2 := Nat.div_le_div_right hSsqLeEll
  have hmod : ℓ % 2 < 2 := Nat.mod_lt _ (by decide)
  have hdiv : ℓ % 2 + 2 * (ℓ / 2) = ℓ := Nat.mod_add_div _ _
  have hcomplLo : lo ≤ ℓ - hi := by dsimp [lo, hi]; omega
  have hcomplHi : ℓ - hi ≤ lo + 1 := by dsimp [lo, hi]; omega
  have hgap : lo + 1 < hi := by
    have hSsq' : 2 ≤ S ^ 2 := by nlinarith [hS]
    dsimp [hi]
    omega
  have hmidCardReal : (mid.card : ℝ) = ∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) := by
    simpa [mid, T, w, lo, hi, boolWeightIndex, Fin.ext_iff] using
      boolFunction_weight_set_card ℓ T
  have hmidMass : (mid.card : ℝ) / (2 : ℝ) ^ ℓ ≤ 1 / 6 := by
    calc
      (mid.card : ℝ) / (2 : ℝ) ^ ℓ =
          (∑ k ∈ T, (Nat.choose ℓ k.val : ℝ)) / (2 : ℝ) ^ ℓ := by rw [hmidCardReal]
      _ = ∑ k ∈ T, (Nat.choose ℓ k.val : ℝ) / (2 : ℝ) ^ ℓ := by rw [Finset.sum_div]
      _ ≤ 1 / 6 := by simpa [T, lo, hi] using centralWeightMass_le_sixth S ℓ hS hℓ
  have hmidSmall : (mid.card : ℝ) ≤ (1 / 6) * (2 : ℝ) ^ ℓ :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ ℓ)).mp hmidMass
  have htotal : low.card + mid.card + high.card = 2 ^ ℓ := by
    have hlow := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin ℓ → Bool))) (p := fun f => w f ≤ lo)
    have hmid := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun f : Fin ℓ → Bool => lo < w f)
      (p := fun f => w f < hi)
    have hcard : (Finset.univ : Finset (Fin ℓ → Bool)).card = 2 ^ ℓ := by simp
    have hlow' : low.card + (Finset.univ.filter fun f : Fin ℓ → Bool => lo < w f).card =
        (Finset.univ : Finset (Fin ℓ → Bool)).card := by
      simpa [low, w, not_le] using hlow
    have hotherHigh :
        (Finset.univ.filter fun f : Fin ℓ → Bool => lo < w f).filter
          (fun f => ¬ w f < hi) = high := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, high]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨lt_of_lt_of_le (by omega : lo < hi) h, h⟩
    have htemp : mid.card +
        ((Finset.univ.filter fun f : Fin ℓ → Bool => lo < w f).filter
          (fun f => ¬ w f < hi)).card =
        (Finset.univ.filter fun f : Fin ℓ → Bool => lo < w f).card := by
      simpa [mid, w, Finset.filter_filter] using hmid
    have hmid' : mid.card + high.card =
        (Finset.univ.filter fun f : Fin ℓ → Bool => lo < w f).card := by
      rw [← hotherHigh]
      exact htemp
    omega
  have hlowToHigh : low.card ≤ high.card := by
    let f : {x : Fin ℓ → Bool // x ∈ low} → {x : Fin ℓ → Bool // x ∈ high} := fun x =>
      ⟨boolComplementEquiv ℓ x.1, by
        have hx := (Finset.mem_filter.mp x.2).2
        simp only [high, Finset.mem_filter, Finset.mem_univ, true_and]
        dsimp [w]
        rw [boolWeight_complement]
        dsimp [w] at hx
        omega⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact (boolComplementEquiv ℓ).injective (congrArg Subtype.val h)
    calc
      low.card = Fintype.card {x : Fin ℓ → Bool // x ∈ low} := (Fintype.card_coe low).symm
      _ ≤ Fintype.card {x : Fin ℓ → Bool // x ∈ high} := Fintype.card_le_of_injective f hinj
      _ = high.card := Fintype.card_coe high
  have hhighToLowBoundary : high.card ≤ low.card + boundary.card := by
    let f : {x : Fin ℓ → Bool // x ∈ high} →
        {x : Fin ℓ → Bool // x ∈ low ∪ boundary} := fun x =>
      ⟨boolComplementEquiv ℓ x.1, by
        have hx := (Finset.mem_filter.mp x.2).2
        simp only [Finset.mem_union, low, boundary, Finset.mem_filter,
          Finset.mem_univ, true_and]
        dsimp [w]
        rw [boolWeight_complement]
        dsimp [w] at hx
        omega⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact (boolComplementEquiv ℓ).injective (congrArg Subtype.val h)
    calc
      high.card = Fintype.card {x : Fin ℓ → Bool // x ∈ high} := (Fintype.card_coe high).symm
      _ ≤ Fintype.card {x : Fin ℓ → Bool // x ∈ low ∪ boundary} := Fintype.card_le_of_injective f hinj
      _ = (low ∪ boundary).card := Fintype.card_coe _
      _ ≤ low.card + boundary.card := Finset.card_union_le _ _
  have hboundarySub : boundary ⊆ mid := by
    intro f hf
    have hf' := (Finset.mem_filter.mp hf).2
    simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp [w] at hf'
    dsimp [w]
    constructor
    · rw [hf']
      omega
    · rw [hf']
      exact hgap
  have hhighSmall : high.card ≤ low.card + mid.card := by
    have hbd := Finset.card_le_card hboundarySub
    omega
  have htotalReal : (low.card : ℝ) + (mid.card : ℝ) + (high.card : ℝ) =
      (2 : ℝ) ^ ℓ := by exact_mod_cast htotal
  have hhighSmallReal : (high.card : ℝ) ≤ (low.card : ℝ) + (mid.card : ℝ) := by
    exact_mod_cast hhighSmall
  have hlowLarge : (1 / 3 : ℝ) * (2 : ℝ) ^ ℓ ≤ (low.card : ℝ) := by
    nlinarith [htotalReal, hhighSmallReal, hmidSmall]
  have hhighLarge : (1 / 3 : ℝ) * (2 : ℝ) ^ ℓ ≤ (high.card : ℝ) :=
    hlowLarge.trans (by exact_mod_cast hlowToHigh)
  constructor
  · simpa [low, w, lo] using hlowLarge
  · simpa [high, w, lo, hi] using hhighLarge

set_option maxHeartbeats 0 in
theorem tag_exists_bound (β γ K : ℝ) (hβ : 0 < β) (hβγ : β ≤ γ)
    (hγ : γ < 1) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, KeyFiber β γ n →
      ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
        (M : Menu4 β γ G n N E X Y) (ρ : FinProb M.ι), N ≤ n * 2 ^ n →
        Balanced ρ M.μ M.ν K → ∃ tag : Key β γ n → M.ι, TagBal M tag (2 * K) := by
  let ω := HypercubeRamsey.omega4 β γ
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hγpos : 0 < γ := lt_of_lt_of_le hβ hβγ
  have hpowω : Tendsto (fun n : ℕ => (n : ℝ) ^ ω) atTop atTop :=
    (_root_.tendsto_rpow_atTop hω).comp tendsto_natCast_atTop_atTop
  have hpowγ : Tendsto (fun n : ℕ => (n : ℝ) ^ γ) atTop atTop :=
    (_root_.tendsto_rpow_atTop hγpos).comp tendsto_natCast_atTop_atTop
  have hexpRatio0 : Tendsto (fun x : ℝ => Real.exp x / x ^ (1 / γ)) atTop atTop :=
    _root_.tendsto_exp_div_rpow_atTop _
  have hexpRatioN0 : Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) ^ γ) / ((n : ℝ) ^ γ) ^ (1 / γ)) atTop atTop :=
    hexpRatio0.comp hpowγ
  have hexpRatioN : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) ^ γ) / (n : ℝ)) atTop atTop := by
    apply hexpRatioN0.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hden : ((n : ℝ) ^ γ) ^ (1 / γ) = (n : ℝ) := by
      rw [← Real.rpow_mul hnreal.le]
      have hpow : γ * (1 / γ) = 1 := by field_simp [ne_of_gt hγpos]
      rw [hpow, Real.rpow_one]
    rw [hden]
  have hscaled : Tendsto
      (fun n : ℕ => (2 * K ^ 2 * Real.exp ((n : ℝ) ^ γ)) / (n : ℝ)) atTop atTop := by
    simpa [mul_div_assoc] using
      hexpRatioN.const_mul_atTop (mul_pos (by norm_num) (sq_pos_of_pos hK))
  obtain ⟨nT, hnT⟩ := Filter.eventually_atTop.1 (hscaled.eventually_ge_atTop (10 : ℝ))
  obtain ⟨nω, hnω⟩ := Filter.eventually_atTop.1 (hpowω.eventually_ge_atTop (50 : ℝ))
  obtain ⟨nγ, hnγ⟩ := Filter.eventually_atTop.1 (hpowγ.eventually_ge_atTop (2 : ℝ))
  refine ⟨max nT (max nω (max nγ 3)), ?_⟩
  intro n hn hKF N E G X Y M ρ hN hbal
  have hn3 : 3 ≤ n :=
    (Nat.le_max_right nγ 3).trans
      ((Nat.le_max_right nω (max nγ 3)).trans
        ((Nat.le_max_right nT (max nω (max nγ 3))).trans hn))
  have hnT' : nT ≤ n := (Nat.le_max_left nT (max nω (max nγ 3))).trans hn
  have hnω' : nω ≤ n :=
    (Nat.le_max_left nω (max nγ 3)).trans
      ((Nat.le_max_right nT (max nω (max nγ 3))).trans hn)
  have hnγ' : nγ ≤ n :=
    (Nat.le_max_left nγ 3).trans
      ((Nat.le_max_right nω (max nγ 3)).trans
        ((Nat.le_max_right nT (max nω (max nγ 3))).trans hn))
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnreal1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hq : 2 ≤ (n : ℝ) ^ γ := hnγ n hnγ'
  have hu : 50 ≤ (n : ℝ) ^ ω := hnω n hnω'
  have htailScale : 10 * (n : ℝ) ≤ 2 * K ^ 2 * Real.exp ((n : ℝ) ^ γ) := by
    have h := hnT n hnT'
    have hnpositive : 0 < (n : ℝ) := hnreal
    exact (le_div_iff₀ hnpositive).mp h
  have hι : Nonempty M.ι := by
    by_contra hι
    haveI : IsEmpty M.ι := not_nonempty_iff.mp hι
    have hs : (∑ i, ρ.w i) = 0 := by simp
    rw [ρ.sum_eq_one] at hs
    norm_num at hs
  let i₀ : M.ι := Classical.choice hι
  have hNpos : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hs := (M.μ i₀).sum_eq_one
    simp at hs
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hEvenNonempty : Nonempty (EvenRole n) := by
    let v : CubeVertex n := fun _ => false
    have hv : IsEvenRole v := by simp [HypercubeRamsey.IsEvenRole, v]
    exact ⟨⟨v, hv⟩⟩
  have hOddNonempty : Nonempty (OddRole n) := by
    let v : CubeVertex n := fun _ => false
    have hv : IsEvenRole v := by simp [HypercubeRamsey.IsEvenRole, v]
    let i : Fin n := ⟨0, by omega⟩
    have hodd : ¬ IsEvenRole (HypercubeRamsey.cubeFlip v i) := by
      intro hflip
      exact (HypercubeRamsey.cubeFlip_parity v i).mp hflip hv
    exact ⟨⟨HypercubeRamsey.cubeFlip v i, hodd⟩⟩
  have hCeNat : 0 < Fintype.card (EvenRole n) := Fintype.card_pos_iff.mpr hEvenNonempty
  have hCoNat : 0 < Fintype.card (OddRole n) := Fintype.card_pos_iff.mpr hOddNonempty
  have hCe : 0 < (Fintype.card (EvenRole n) : ℝ) := by exact_mod_cast hCeNat
  have hCo : 0 < (Fintype.card (OddRole n) : ℝ) := by exact_mod_cast hCoNat
  let q : ℝ := (n : ℝ) ^ γ
  let A : ℝ := (n : ℝ) ^ (γ + ω) / 10
  let B : ℝ := Real.exp (2 * q)
  let ε : ℝ := Real.exp (-A)
  have hAeq : A = q * (n : ℝ) ^ ω / 10 := by
    dsimp [A, q]
    rw [Real.rpow_add hnreal]
  have hfactor : 1 ≤ (n : ℝ) ^ ω / 10 - 4 := by nlinarith [hu]
  have hqnonneg : 0 ≤ q := Real.rpow_nonneg hnreal.le _
  have hqA : q ≤ A - 4 * q := by
    have hmul := mul_le_mul_of_nonneg_left hfactor hqnonneg
    rw [hAeq]
    nlinarith
  have hBpos : 0 < B := by positivity
  have hBsq : B ^ 2 = Real.exp (4 * q) := by
    dsimp [B]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  let p : FinProb (Key β γ n → M.ι) := FinProb.pi (fun _ : Key β γ n => ρ)
  let fibE : Key β γ n → Finset (EvenRole n) := fun κ =>
    Finset.univ.filter fun a => key β γ n a.1 = κ
  let fibO : Key β γ n → Finset (OddRole n) := fun κ =>
    Finset.univ.filter fun u => key β γ n u.1 = κ
  let αE : Key β γ n → ℝ := fun κ =>
    (Fintype.card (EvenRole n) : ℝ)⁻¹ * (fibE κ).card
  let αO : Key β γ n → ℝ := fun κ =>
    (Fintype.card (OddRole n) : ℝ)⁻¹ * (fibO κ).card
  have hαESum : ∑ κ, αE κ = 1 := by
    dsimp [αE]
    rw [← Finset.mul_sum]
    have hc := sum_fiber_card_eq_card (fun a : EvenRole n => key β γ n a.1)
    rw [hc]
    field_simp [ne_of_gt hCe]
  have hαOSum : ∑ κ, αO κ = 1 := by
    dsimp [αO]
    rw [← Finset.mul_sum]
    have hc := sum_fiber_card_eq_card (fun u : OddRole n => key β γ n u.1)
    rw [hc]
    field_simp [ne_of_gt hCo]
  have hαENonneg : ∀ κ, 0 ≤ αE κ := by
    intro κ
    dsimp [αE]
    positivity
  have hαONonneg : ∀ κ, 0 ≤ αO κ := by
    intro κ
    dsimp [αO]
    positivity
  have hαELe : ∀ κ, αE κ ≤ ε := by
    intro κ
    have h := (hKF κ).1
    have hExp : Real.exp (-A) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
    have hExp' : Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ)) / 10) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
      ring
    have hfiber :
        ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
          Real.exp (-A) * Fintype.card (EvenRole n) := by
      rw [hExp, ← hExp']
      exact h
    dsimp [αE, fibE]
    have hInv : 0 ≤ (Fintype.card (EvenRole n) : ℝ)⁻¹ := inv_nonneg.mpr hCe.le
    calc
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) ≤
        (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          (Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) * Fintype.card (EvenRole n)) :=
            mul_le_mul_of_nonneg_left hfiber hInv
      _ = Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) := by
        field_simp [ne_of_gt hCe]
  have hαOLe : ∀ κ, αO κ ≤ ε := by
    intro κ
    have h := (hKF κ).2
    have hExp : Real.exp (-A) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
    have hExp' : Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ)) / 10) =
        Real.exp (-((n : ℝ) ^ (γ + HypercubeRamsey.omega4 β γ) / 10)) := by
      congr 1
      ring
    have hfiber :
        ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
          Real.exp (-A) * Fintype.card (OddRole n) := by
      rw [hExp, ← hExp']
      exact h
    dsimp [αO, fibO]
    have hInv : 0 ≤ (Fintype.card (OddRole n) : ℝ)⁻¹ := inv_nonneg.mpr hCo.le
    calc
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) ≤
        (Fintype.card (OddRole n) : ℝ)⁻¹ *
          (Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) * Fintype.card (OddRole n)) :=
            mul_le_mul_of_nonneg_left hfiber hInv
      _ = Real.exp (-((n : ℝ) ^ (γ + ω) / 10)) := by
        field_simp [ne_of_gt hCo]
  have hαSq_le (α : Key β γ n → ℝ) (hsum : ∑ κ, α κ = 1)
      (hnonneg : ∀ κ, 0 ≤ α κ) (hle : ∀ κ, α κ ≤ ε) :
      ∑ κ, (α κ * B) ^ 2 ≤ ε * B ^ 2 := by
    have hsq : ∑ κ, α κ ^ 2 ≤ ε := by
      calc
        ∑ κ, α κ ^ 2 ≤ ∑ κ, ε * α κ := by
          apply Finset.sum_le_sum
          intro κ hκ
          have hprod := mul_nonneg (hnonneg κ) (sub_nonneg.mpr (hle κ))
          nlinarith
        _ = ε * 1 := by rw [← Finset.mul_sum, hsum]
        _ = ε := by ring
    calc
      ∑ κ, (α κ * B) ^ 2 = (∑ κ, α κ ^ 2) * B ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro κ hκ
        rw [mul_pow]
      _ ≤ ε * B ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg B)
  have hαSq_pos (α : Key β γ n → ℝ) (hsum : ∑ κ, α κ = 1)
      (hnonneg : ∀ κ, 0 ≤ α κ) (hB : 0 < B) :
      0 < ∑ κ, (α κ * B) ^ 2 := by
    have hhas : ∃ κ, 0 < α κ := by
      by_contra h
      push_neg at h
      have hz : ∀ κ, α κ = 0 := by
        intro κ
        exact le_antisymm (h κ) (hnonneg κ)
      have hzero : ∑ κ, α κ = 0 := by simp [hz]
      rw [hsum] at hzero
      norm_num at hzero
    obtain ⟨κ, hκ⟩ := hhas
    have hterm : 0 < (α κ * B) ^ 2 := sq_pos_of_pos (mul_pos hκ hB)
    have hle : (α κ * B) ^ 2 ≤ ∑ j, (α j * B) ^ 2 :=
      Finset.single_le_sum (fun j hj => sq_nonneg (α j * B)) (Finset.mem_univ κ)
    exact hterm.trans_le hle
  have hVarEpos : 0 < ∑ κ, (αE κ * B) ^ 2 :=
    hαSq_pos αE hαESum hαENonneg hBpos
  have hVarOpos : 0 < ∑ κ, (αO κ * B) ^ 2 :=
    hαSq_pos αO hαOSum hαONonneg hBpos
  have hVeq : ε * B ^ 2 = Real.exp (4 * q - A) := by
    dsimp [ε]
    rw [hBsq, ← Real.exp_add]
    congr 1
    ring
  have hVarEle : ∑ κ, (αE κ * B) ^ 2 ≤ Real.exp (4 * q - A) :=
    (hαSq_le αE hαESum hαENonneg hαELe).trans_eq hVeq
  have hVarOle : ∑ κ, (αO κ * B) ^ 2 ≤ Real.exp (4 * q - A) :=
    (hαSq_le αO hαOSum hαONonneg hαOLe).trans_eq hVeq
  have hVpos : 0 < Real.exp (4 * q - A) := Real.exp_pos _
  have hVinv : (Real.exp (4 * q - A))⁻¹ = Real.exp (A - 4 * q) := by
    rw [show 4 * q - A = -(A - 4 * q) by ring, Real.exp_neg, inv_inv]
  have htailFrom (S : ℝ) (hSpos : 0 < S) (hSle : S ≤ Real.exp (4 * q - A)) :
      2 * Real.exp (-2 * K ^ 2 / S) ≤ 2 * Real.exp (-10 * (n : ℝ)) := by
    have hInv : (Real.exp (4 * q - A))⁻¹ ≤ S⁻¹ :=
      (inv_le_inv₀ hVpos hSpos).2 hSle
    have hExpLarge : Real.exp q ≤ S⁻¹ := by
      calc
        Real.exp q ≤ Real.exp (A - 4 * q) := Real.exp_le_exp.mpr hqA
        _ = (Real.exp (4 * q - A))⁻¹ := hVinv.symm
        _ ≤ S⁻¹ := hInv
    have hscale : 10 * (n : ℝ) ≤ 2 * K ^ 2 * S⁻¹ := by
      calc
        10 * (n : ℝ) ≤ 2 * K ^ 2 * Real.exp q := htailScale
        _ ≤ 2 * K ^ 2 * S⁻¹ := mul_le_mul_of_nonneg_left hExpLarge (by positivity)
    apply (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).2
    apply Real.exp_le_exp.mpr
    rw [div_eq_mul_inv]
    nlinarith
  have hsXbound (i : M.ι) : M.sX i ≤ 2 * q := by
    rcases M.prep i with ⟨_, hsX, _, _, _, _, _, _, _⟩
    have hqQ : 2 ≤ q := by simpa [q] using hq
    calc
      M.sX i ≤ 3 / 2 * (n : ℝ) ^ β := hsX
      _ ≤ 3 / 2 * q := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnreal1 hβγ) (by norm_num)
      _ ≤ 2 * q := by nlinarith [hqQ]
  have hsYbound (i : M.ι) : M.sY i + 1 ≤ 2 * q := by
    rcases M.prep i with ⟨_, _, _, hsY, _, _, _, _, _⟩
    have hqQ : 2 ≤ q := by simpa [q] using hq
    calc
      M.sY i + 1 ≤ 3 / 2 * q + 1 := by
        simpa [add_comm] using add_le_add_right hsY 1
      _ ≤ 2 * q := by linarith [hqQ]
  have hfEven (x : Fin N) (i : M.ι) :
      0 ≤ (N : ℝ) * (M.μ i).w x ∧ (N : ℝ) * (M.μ i).w x ≤ B := by
    rcases M.prep i with ⟨_, _, _, _, hwidth, _, _, _, _⟩
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) ((M.μ i).nonneg x)
    · calc
        (N : ℝ) * (M.μ i).w x ≤
            (N : ℝ) * (Real.exp (M.sX i) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hwidth x) (Nat.cast_nonneg _)
        _ = Real.exp (M.sX i) := by field_simp [ne_of_gt hNreal]
        _ ≤ B := Real.exp_le_exp.mpr (hsXbound i)
  have hfOdd (y : Fin N) (i : M.ι) :
      0 ≤ (N : ℝ) * (M.ν i).w y ∧ (N : ℝ) * (M.ν i).w y ≤ B := by
    rcases M.prep i with ⟨_, _, _, _, _, hwidth, _, _, _⟩
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) ((M.ν i).nonneg y)
    · calc
        (N : ℝ) * (M.ν i).w y ≤
            (N : ℝ) * (Real.exp (M.sY i + 1) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (hwidth y) (Nat.cast_nonneg _)
        _ = Real.exp (M.sY i + 1) := by field_simp [ne_of_gt hNreal]
        _ ≤ B := Real.exp_le_exp.mpr (hsYbound i)
  have hmeanEven (x : Fin N) :
      ρ.expect (fun i => (N : ℝ) * (M.μ i).w x) ≤ K := by
    have hb := hbal.1 x
    unfold FinProb.expect
    calc
      (∑ i, ρ.w i * ((N : ℝ) * (M.μ i).w x)) =
          (N : ℝ) * ∑ i, ρ.w i * (M.μ i).w x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (N : ℝ) * (K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = K := by field_simp [ne_of_gt hNreal]
  have hmeanOdd (y : Fin N) :
      ρ.expect (fun i => (N : ℝ) * (M.ν i).w y) ≤ K := by
    have hb := hbal.2 y
    unfold FinProb.expect
    calc
      (∑ i, ρ.w i * ((N : ℝ) * (M.ν i).w y)) =
          (N : ℝ) * ∑ i, ρ.w i * (M.ν i).w y := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ (N : ℝ) * (K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      _ = K := by field_simp [ne_of_gt hNreal]
  let δ : ℝ := 2 * Real.exp (-10 * (n : ℝ))
  have htailE (x : Fin N) : p.pr (fun tag : Key β γ n → M.ι =>
      2 * K < ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x)) ≤ δ := by
    calc
      p.pr (fun tag : Key β γ n → M.ι =>
          2 * K < ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x)) ≤
        2 * Real.exp (-2 * K ^ 2 / ∑ κ, (αE κ * B) ^ 2) := by
          exact weightedTag_tail ρ αE B K hαESum hαENonneg hVarEpos
            (fun i => (N : ℝ) * (M.μ i).w x) (hfEven x) (hmeanEven x) hK
      _ ≤ δ := by
        dsimp [δ]
        exact htailFrom _ hVarEpos hVarEle
  have htailO (y : Fin N) : p.pr (fun tag : Key β γ n → M.ι =>
      2 * K < ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y)) ≤ δ := by
    calc
      p.pr (fun tag : Key β γ n → M.ι =>
          2 * K < ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y)) ≤
        2 * Real.exp (-2 * K ^ 2 / ∑ κ, (αO κ * B) ^ 2) := by
          exact weightedTag_tail ρ αO B K hαOSum hαONonneg hVarOpos
            (fun i => (N : ℝ) * (M.ν i).w y) (hfOdd y) (hmeanOdd y) hK
      _ ≤ δ := by
        dsimp [δ]
        exact htailFrom _ hVarOpos hVarOle
  let badE : Fin N → (Key β γ n → M.ι) → Prop := fun x tag =>
    2 * K < ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x)
  let badO : Fin N → (Key β γ n → M.ι) → Prop := fun y tag =>
    2 * K < ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y)
  let badLabel : Fin N ⊕ Fin N → (Key β γ n → M.ι) → Prop := fun z tag =>
    match z with
    | Sum.inl x => badE x tag
    | Sum.inr y => badO y tag
  let Bad : (Key β γ n → M.ι) → Prop := fun tag => ∃ z, badLabel z tag
  have hsumE : ∑ x : Fin N, p.pr (badE x) ≤ (N : ℝ) * δ := by
    calc
      ∑ x : Fin N, p.pr (badE x) ≤ ∑ _x : Fin N, δ :=
        Finset.sum_le_sum fun x hx => htailE x
      _ = (N : ℝ) * δ := by simp
  have hsumO : ∑ y : Fin N, p.pr (badO y) ≤ (N : ℝ) * δ := by
    calc
      ∑ y : Fin N, p.pr (badO y) ≤ ∑ _y : Fin N, δ :=
        Finset.sum_le_sum fun y hy => htailO y
      _ = (N : ℝ) * δ := by simp
  have hsumBad : p.pr Bad ≤ 2 * (N : ℝ) * δ := by
    calc
      p.pr Bad ≤ ∑ z : Fin N ⊕ Fin N, p.pr (badLabel z) := pr_exists_le p badLabel
      _ = (∑ x : Fin N, p.pr (badE x)) + ∑ y : Fin N, p.pr (badO y) := by
        simp [badLabel, Fintype.sum_sum_type]
      _ ≤ (N : ℝ) * δ + (N : ℝ) * δ := add_le_add hsumE hsumO
      _ = 2 * (N : ℝ) * δ := by ring
  have hNrealUpper : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hN
  have hlog4n : Real.log (4 * (n : ℝ)) ≤ 4 * (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 4 * (n : ℝ))
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    linarith
  have hpow2 : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hnumer : 4 * (n : ℝ) * (2 : ℝ) ^ n =
      Real.exp (Real.log (4 * (n : ℝ)) + (n : ℝ) * Real.log 2) := by
    calc
      4 * (n : ℝ) * (2 : ℝ) ^ n =
          Real.exp (Real.log (4 * (n : ℝ))) * Real.exp ((n : ℝ) * Real.log 2) := by
            rw [Real.exp_log (by positivity : 0 < 4 * (n : ℝ)), hpow2]
      _ = Real.exp (Real.log (4 * (n : ℝ)) + (n : ℝ) * Real.log 2) :=
        (Real.exp_add _ _).symm
  have hlogPower : (n : ℝ) * Real.log 2 ≤ (n : ℝ) := by
    calc
      (n : ℝ) * Real.log 2 ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg n)
      _ = (n : ℝ) := by ring
  have hlogTotal : Real.log (4 * (n : ℝ)) + (n : ℝ) * Real.log 2 ≤ 5 * (n : ℝ) := by
    linarith [hlog4n, hlogPower]
  have hnumLe : 4 * (n : ℝ) * (2 : ℝ) ^ n ≤ Real.exp (5 * (n : ℝ)) := by
    rw [hnumer]
    exact Real.exp_le_exp.mpr hlogTotal
  have hsmall : 4 * (n : ℝ) * (2 : ℝ) ^ n * Real.exp (-10 * (n : ℝ)) < 1 := by
    calc
      4 * (n : ℝ) * (2 : ℝ) ^ n * Real.exp (-10 * (n : ℝ)) ≤
          Real.exp (5 * (n : ℝ)) * Real.exp (-10 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hnumLe (Real.exp_nonneg _)
      _ = Real.exp (-5 * (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ < 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_lt_exp.mpr
        have hnpos : 0 < (n : ℝ) := hnreal
        linarith
  have hbadlt : p.pr Bad < 1 := by
    calc
      p.pr Bad ≤ 2 * (N : ℝ) * δ := hsumBad
      _ = 4 * (N : ℝ) * Real.exp (-10 * (n : ℝ)) := by dsimp [δ]; ring
      _ ≤ 4 * (n : ℝ) * (2 : ℝ) ^ n * Real.exp (-10 * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        nlinarith [hNrealUpper]
      _ < 1 := hsmall
  have hgoodprob : p.pr (fun tag => ¬ Bad tag) > 0 := by
    have h := HypercubeRamsey.S04.pr_add_pr_not p Bad
    linarith
  have hgood : ∃ tag : Key β γ n → M.ι, ¬ Bad tag := by
    by_contra h
    push_neg at h
    have hzero : p.pr (fun tag => ¬ Bad tag) = 0 := by
      unfold FinProb.pr
      apply Finset.sum_eq_zero
      intro tag htag
      simp [h tag]
    linarith
  obtain ⟨tag, htag⟩ := hgood
  have hAvgE (tag : Key β γ n → M.ι) (x : Fin N) :
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
        ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x =
      ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x) := by
    calc
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x =
        (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ∑ κ, ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ) *
            ((N : ℝ) * (M.μ (tag κ)).w x) := by
          congr 1
          exact sum_eq_sum_fiber_card (fun a : EvenRole n => key β γ n a.1)
            (fun κ => (N : ℝ) * (M.μ (tag κ)).w x)
      _ = ∑ κ, ((Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun a : EvenRole n => key β γ n a.1 = κ).card : ℝ)) *
            ((N : ℝ) * (M.μ (tag κ)).w x) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro κ hκ
          ring
      _ = ∑ κ, αE κ * ((N : ℝ) * (M.μ (tag κ)).w x) := by
          apply Finset.sum_congr rfl
          intro κ hκ
          simp [αE, fibE]
  have hAvgO (tag : Key β γ n → M.ι) (y : Fin N) :
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
        ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y =
      ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y) := by
    calc
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y =
        (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ∑ κ, ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ) *
            ((N : ℝ) * (M.ν (tag κ)).w y) := by
          congr 1
          exact sum_eq_sum_fiber_card (fun u : OddRole n => key β γ n u.1)
            (fun κ => (N : ℝ) * (M.ν (tag κ)).w y)
      _ = ∑ κ, ((Fintype.card (OddRole n) : ℝ)⁻¹ *
          ((Finset.univ.filter fun u : OddRole n => key β γ n u.1 = κ).card : ℝ)) *
            ((N : ℝ) * (M.ν (tag κ)).w y) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro κ hκ
          ring
      _ = ∑ κ, αO κ * ((N : ℝ) * (M.ν (tag κ)).w y) := by
          apply Finset.sum_congr rfl
          intro κ hκ
          simp [αO, fibO]
  have hgoodE : ∀ x : Fin N,
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
        ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x ≤ 2 * K := by
    intro x
    by_contra h
    have hlt : 2 * K <
        (Fintype.card (EvenRole n) : ℝ)⁻¹ *
          ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x := lt_of_not_ge h
    apply htag
    refine ⟨Sum.inl x, ?_⟩
    dsimp [badLabel, badE]
    rw [← hAvgE tag x]
    exact hlt
  have hgoodO : ∀ y : Fin N,
      (Fintype.card (OddRole n) : ℝ)⁻¹ *
        ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y ≤ 2 * K := by
    intro y
    by_contra h
    have hlt : 2 * K <
        (Fintype.card (OddRole n) : ℝ)⁻¹ *
          ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y := lt_of_not_ge h
    apply htag
    refine ⟨Sum.inr y, ?_⟩
    dsimp [badLabel, badO]
    rw [← hAvgO tag y]
    exact hlt
  refine ⟨tag, ?_⟩
  change (∀ x, (Fintype.card (EvenRole n) : ℝ)⁻¹ *
      ∑ a : EvenRole n, (N : ℝ) * (M.μ (tag (key β γ n a.1))).w x ≤ 2 * K) ∧
    (∀ y, (Fintype.card (OddRole n) : ℝ)⁻¹ *
      ∑ u : OddRole n, (N : ℝ) * (M.ν (tag (key β γ n u.1))).w y ≤ 2 * K)
  exact ⟨hgoodE, hgoodO⟩

private theorem gadgetPower_le_four {β γ : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hω : 0 < HypercubeRamsey.omega4 β γ) :
    (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) ≤
      4 * (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ) := by
  let x : ℝ := (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ)
  let q : ℕ := ⌈Real.log x / Real.log 2⌉₊
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hxone : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hnreal (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 0 ≤ Real.log x / Real.log 2 := div_nonneg hlogx hlog2.le
  have hq : (q : ℝ) < Real.log x / Real.log 2 + 1 := Nat.ceil_lt_add_one hratio
  have hmaxNat : max 1 q ≤ q + 1 := by omega
  have hmax : (max 1 q : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hmaxNat
  have hbound : (max 1 q : ℝ) ≤ Real.log x / Real.log 2 + 2 := by linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hbound
  have hcast : (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) =
      Real.rpow 2 (max 1 q : ℝ) := by
    unfold HypercubeRamsey.S04.gadgetPower
    rw [Nat.cast_pow]
    rw [← Real.rpow_natCast]
    congr 1
    simp [Nat.cast_max, q, x]
  have heval : Real.rpow 2 (Real.log x / Real.log 2 + 2) = 4 * x := by
    change (2 : ℝ) ^ (Real.log x / Real.log 2 + 2) = 4 * x
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hmul : Real.log 2 * (Real.log x / Real.log 2 + 2) =
        (Real.log x + Real.log 2) + Real.log 2 := by
      field_simp [ne_of_gt hlog2]
      ring
    rw [hmul, Real.exp_add, Real.exp_add, Real.exp_log hxpos,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  calc
    (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) = Real.rpow 2 (max 1 q : ℝ) := hcast
    _ ≤ Real.rpow 2 (Real.log x / Real.log 2 + 2) := hpow
    _ = 4 * x := heval

theorem gadgetPower_ge_scale {β γ : ℝ} (n : ℕ)
    (hω : 0 < HypercubeRamsey.omega4 β γ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ) ≤
      (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) := by
  let x : ℝ := (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ)
  let t : ℝ := Real.log x / Real.log 2
  let q : ℕ := ⌈t⌉₊
  have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hxpos : 0 < x := by
    dsimp [x]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hxone : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow hnreal (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 0 ≤ t := by dsimp [t]; exact div_nonneg hlogx hlog2.le
  have htceil : t ≤ (q : ℝ) := Nat.le_ceil t
  have hqmax : (q : ℝ) ≤ (max 1 q : ℝ) := by
    exact_mod_cast (Nat.le_max_right 1 q)
  have htmax : t ≤ (max 1 q : ℝ) := htceil.trans hqmax
  have hcast : (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) =
      Real.rpow 2 (max 1 q : ℝ) := by
    unfold HypercubeRamsey.S04.gadgetPower
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    congr 1
    simp [Nat.cast_max, q, t, x]
  have hxeq : x = Real.rpow 2 t := by
    calc
      x = Real.exp (Real.log x) := (Real.exp_log hxpos).symm
      _ = Real.exp (Real.log 2 * t) := by
        congr 1
        dsimp [t]
        field_simp [ne_of_gt hlog2]
      _ = Real.rpow 2 t := (Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) t).symm
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2) htmax
  calc
    (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ) = x := by rfl
    _ = Real.rpow 2 t := hxeq
    _ ≤ Real.rpow 2 (max 1 q : ℝ) := hpow
    _ = (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) := hcast.symm

theorem gadgetPower_even {β γ : ℝ} (n : ℕ) :
    Even (HypercubeRamsey.S04.gadgetPower β γ n) := by
  unfold HypercubeRamsey.S04.gadgetPower
  apply (Nat.even_pow).2
  constructor
  · norm_num
  · have h := Nat.le_max_left 1
      (⌈Real.log ((n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ)) / Real.log 2⌉₊)
    omega

theorem leaf_choice_tail (S G s : ℕ) (x : ℝ)
    (hSpos : 0 < (S : ℝ)) (hlogS : Real.log (S : ℝ) ≤ (s : ℝ) / 12)
    (hlog32 : 1 / 3 ≤ Real.log ((3 : ℝ) / 2)) (hx : 0 ≤ x)
    (hchunks : (81 / 100 : ℝ) * x ≤ (G : ℝ) * (s : ℝ)) :
    (S : ℝ) ^ G * ((2 : ℝ) / 3) ^ (G * s) ≤ Real.exp (-x / 10) := by
  have hlog23 : Real.log ((2 : ℝ) / 3) = -Real.log ((3 : ℝ) / 2) := by
    have hi : ((3 : ℝ) / 2)⁻¹ = (2 : ℝ) / 3 := by norm_num
    rw [← hi, Real.log_inv]
  have hpowS : (S : ℝ) ^ G = Real.exp ((G : ℝ) * Real.log (S : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hSpos]
    congr 1
    ring
  have hpowFrac : ((2 : ℝ) / 3) ^ (G * s) =
      Real.exp (((G * s : ℕ) : ℝ) * Real.log ((2 : ℝ) / 3)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ) / 3)]
    congr 1
    ring
  have hscale :
      (G : ℝ) * Real.log (S : ℝ) - ((G * s : ℕ) : ℝ) * Real.log ((3 : ℝ) / 2) ≤
        -((G * s : ℕ) : ℝ) / 4 := by
    have hGnonneg : 0 ≤ (G : ℝ) := Nat.cast_nonneg _
    have hGsnonneg : 0 ≤ ((G * s : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hlogS hGnonneg
    have h2 := mul_le_mul_of_nonneg_left hlog32 hGsnonneg
    have h1' : (G : ℝ) * Real.log (S : ℝ) ≤ ((G * s : ℕ) : ℝ) / 12 := by
      rw [Nat.cast_mul]
      calc
        (G : ℝ) * Real.log (S : ℝ) ≤ (G : ℝ) * ((s : ℝ) / 12) := h1
        _ = (G : ℝ) * (s : ℝ) / 12 := by ring
    have h2' : ((G * s : ℕ) : ℝ) / 3 ≤
        ((G * s : ℕ) : ℝ) * Real.log ((3 : ℝ) / 2) := by
      simpa [Nat.cast_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h2
    linarith [h1', h2']
  have hchunks' : (81 / 100 : ℝ) * x ≤ ((G * s : ℕ) : ℝ) := by
    simpa [Nat.cast_mul] using hchunks
  have hscale' : -((G * s : ℕ) : ℝ) / 4 ≤ -x / 10 := by nlinarith [hchunks']
  calc
    (S : ℝ) ^ G * ((2 : ℝ) / 3) ^ (G * s) =
        Real.exp ((G : ℝ) * Real.log (S : ℝ) - ((G * s : ℕ) : ℝ) * Real.log ((3 : ℝ) / 2)) := by
          rw [hpowS, hpowFrac, hlog23, ← Real.exp_add]
          congr 1
          push_cast
          ring
    _ ≤ Real.exp (-((G * s : ℕ) : ℝ) / 4) := Real.exp_le_exp.mpr hscale
    _ ≤ Real.exp (-x / 10) := Real.exp_le_exp.mpr hscale'

private theorem specialNum_le_const {β γ : ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
      16384 * (n : ℝ) ^ (γ + 13 * HypercubeRamsey.omega4 β γ) := by
  let ω := HypercubeRamsey.omega4 β γ
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have hωγ : ω < γ := by
    dsimp [ω, HypercubeRamsey.omega4]
    have hm : min β (1 - γ) ≤ β := min_le_left _ _
    have hb : β / 1000 < β := by nlinarith
    linarith
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hG : (G : ℝ) ≤ (n : ℝ) ^ (γ - ω) := by
    dsimp [G, HypercubeRamsey.S04.gadgetNum, ω]
    exact Nat.floor_le (Real.rpow_nonneg hnreal.le _)
  have hS := gadgetPower_le_four n hn hω
  have hs : (s : ℝ) ≤ (HypercubeRamsey.S04.gadgetPower β γ n : ℝ) := by
    exact_mod_cast (Nat.sub_le (HypercubeRamsey.S04.gadgetPower β γ n) 1)
  have hs' : (s : ℝ) ≤ 4 * (n : ℝ) ^ (2 * ω) := hs.trans hS
  have hnonnegG : 0 ≤ (G : ℝ) := Nat.cast_nonneg _
  have hnonnegs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hprod : (G : ℝ) * (s : ℝ) * (s : ℝ) ^ 6 ≤
      (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 := by
    calc
      (G : ℝ) * (s : ℝ) * (s : ℝ) ^ 6 ≤
          (n : ℝ) ^ (γ - ω) * (s : ℝ) * (s : ℝ) ^ 6 := by
        gcongr
      _ = (n : ℝ) ^ (γ - ω) * (s : ℝ) ^ 7 := by ring
      _ ≤ (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 := by
        gcongr
  have hpow : ((n : ℝ) ^ (2 * ω)) ^ 7 = (n : ℝ) ^ (14 * ω) := by
    rw [Real.rpow_pow_comm hnreal.le (2 * ω) 7]
    rw [← Real.rpow_natCast_mul hnreal.le 7 (2 * ω)]
    congr 1
    ring
  have hproduct : (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 =
      16384 * (n : ℝ) ^ (γ + 13 * ω) := by
    calc
      (n : ℝ) ^ (γ - ω) * (4 * (n : ℝ) ^ (2 * ω)) ^ 7 =
          (n : ℝ) ^ (γ - ω) * (4 ^ 7 * ((n : ℝ) ^ (2 * ω)) ^ 7) := by rw [mul_pow]
      _ = 4 ^ 7 * ((n : ℝ) ^ (γ - ω) * (n : ℝ) ^ (14 * ω)) := by rw [hpow]; ring
      _ = 4 ^ 7 * (n : ℝ) ^ (γ - ω + 14 * ω) := by rw [← Real.rpow_add hnreal]
      _ = 16384 * (n : ℝ) ^ (γ + 13 * ω) := by norm_num; congr 1 <;> ring
  have hspecial : (HypercubeRamsey.S04.specialNum β γ n : ℝ) =
      (G : ℝ) * (s : ℝ) * (s : ℝ) ^ 6 := by
    simp [HypercubeRamsey.S04.specialNum, HypercubeRamsey.S04.chunkLen, G, s, ℓ,
      Nat.cast_mul, Nat.cast_pow, Nat.mul_assoc]
    ring
  rw [hspecial]
  exact hprod.trans_eq hproduct

theorem specialNum_eventually_bound {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
        (n : ℝ) ^ (γ + 14 * HypercubeRamsey.omega4 β γ) := by
  let ω := HypercubeRamsey.omega4 β γ
  have hω : 0 < ω := HypercubeRamsey.S04.omega4_pos hβ hγ
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ω) atTop atTop :=
    (_root_.tendsto_rpow_atTop hω).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (16384 : ℝ))
  refine ⟨max n₁ 2, ?_⟩
  intro n hn
  have hnlarge : 16384 ≤ (n : ℝ) ^ ω := hn₁ n (le_trans (Nat.le_max_left _ _) hn)
  have hn2 : 2 ≤ n := le_trans (Nat.le_max_right _ _) hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpow_nonneg : 0 ≤ (n : ℝ) ^ (γ + 13 * ω) := Real.rpow_nonneg hnreal.le _
  calc
    (HypercubeRamsey.S04.specialNum β γ n : ℝ) ≤
        16384 * (n : ℝ) ^ (γ + 13 * ω) := specialNum_le_const n hn2 hβ hβγ hγ
    _ ≤ (n : ℝ) ^ ω * (n : ℝ) ^ (γ + 13 * ω) :=
      mul_le_mul_of_nonneg_right hnlarge hpow_nonneg
    _ = (n : ℝ) ^ (γ + 14 * ω) := by
      rw [← Real.rpow_add hnreal]
      congr 1
      ring

theorem keyFiber_growth_thresholds {β γ : ℝ}
    (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      128 ≤ (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ) ∧
      10 ≤ (n : ℝ) ^ (γ - HypercubeRamsey.omega4 β γ) := by
  have hω : 0 < HypercubeRamsey.omega4 β γ :=
    HypercubeRamsey.S04.omega4_pos hβ hγ
  have hωltγ : HypercubeRamsey.omega4 β γ < γ := by
    dsimp [HypercubeRamsey.omega4]
    have hmin : min β (1 - γ) ≤ β := min_le_left _ _
    have hdiv : β / 1000 < β := by nlinarith
    linarith
  have hT₁ : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (mul_pos (by norm_num) hω)).comp
      tendsto_natCast_atTop_atTop
  have hT₂ : Tendsto
      (fun n : ℕ => (n : ℝ) ^ (γ - HypercubeRamsey.omega4 β γ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hωltγ)).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1
    (hT₁.eventually_ge_atTop (128 : ℝ))
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1
    (hT₂.eventually_ge_atTop (10 : ℝ))
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := (le_max_left n₁ n₂).trans hn
  have hn₂' : n₂ ≤ n := (le_max_right n₁ n₂).trans hn
  exact ⟨hn₁ n hn₁', hn₂ n hn₂'⟩

theorem keyLocal_le_specialNum {β γ : ℝ} (n : ℕ) :
    ∀ v : CubeVertex n,
      ((Finset.univ.filter fun i : Fin n =>
        HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) ≠
          HypercubeRamsey.S04.key β γ n v).card : ℝ) ≤
        (HypercubeRamsey.S04.specialNum β γ n : ℝ) := by
  classical
  intro v
  let S : Finset (Fin n) := Finset.univ.filter fun i => i.val < HypercubeRamsey.S04.specialNum β γ n
  have hsub : (Finset.univ.filter fun i : Fin n =>
      HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) ≠
        HypercubeRamsey.S04.key β γ n v) ⊆ S := by
    intro i hi
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hge
    have hnot : ∀ g : Fin (HypercubeRamsey.S04.gadgetNum β γ n),
        ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
          i ∉ HypercubeRamsey.S04.chunkCoords β γ n g j := by
      intro g j hmem
      have hlt := chunkCoords_below_specialNum g j hmem
      omega
    have hkey : HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) =
        HypercubeRamsey.S04.key β γ n v := by
      funext g
      exact gadgetOut_flip_eq g v i (hnot g)
    have hneq : HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip v i) ≠
        HypercubeRamsey.S04.key β γ n v := (Finset.mem_filter.mp hi).2
    exact hneq hkey
  have hcard : S.card ≤ HypercubeRamsey.S04.specialNum β γ n := by
    calc
      S.card = Fintype.card {i : Fin n // i ∈ S} := by simp
      _ ≤ Fintype.card (Fin (HypercubeRamsey.S04.specialNum β γ n)) :=
        Fintype.card_le_of_injective
          (fun i => (⟨i.1.val, (Finset.mem_filter.mp i.2).2⟩ : Fin (HypercubeRamsey.S04.specialNum β γ n)))
          (by
            intro a b h
            apply Subtype.ext
            apply Fin.ext
            simpa using congrArg Fin.val h)
      _ = HypercubeRamsey.S04.specialNum β γ n := Fintype.card_fin _
  have hle := Finset.card_le_card hsub
  exact_mod_cast hle.trans hcard

private theorem card_exists_finite_constraints_le_sum {ι α : Type*} [Fintype ι] [Fintype α]
    (A : ι → Finset α) :
    (Finset.univ.filter fun x : α => ∃ i, x ∈ A i).card ≤ ∑ i, (A i).card := by
  classical
  let f : {x : α // ∃ i, x ∈ A i} → Σ i, {x : α // x ∈ A i} := fun x =>
    ⟨Classical.choose x.2, ⟨x.1, Classical.choose_spec x.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z => z.2.1) h
  calc
    (Finset.univ.filter fun x : α => ∃ i, x ∈ A i).card =
        Fintype.card {x : α // ∃ i, x ∈ A i} := by
          let U : Finset α := Finset.univ.filter fun x => ∃ i, x ∈ A i
          have hmem (x : α) : x ∈ U ↔ ∃ i, x ∈ A i := by simp [U]
          let e : {x : α // x ∈ U} ≃ {x : α // ∃ i, x ∈ A i} := {
            toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
            invFun := fun x => ⟨x.1, (hmem x.1).mpr x.2⟩
            left_inv := by intro x; apply Subtype.ext; rfl
            right_inv := by intro x; apply Subtype.ext; rfl
          }
          calc
            U.card = Fintype.card {x : α // x ∈ U} := (Fintype.card_coe U).symm
            _ = Fintype.card {x : α // ∃ i, x ∈ A i} := Fintype.card_congr e
    _ ≤ Fintype.card (Σ i, {x : α // x ∈ A i}) := Fintype.card_le_of_injective f hf
    _ = ∑ i, (A i).card := by simp

private theorem clipped_eq_blockWeight_of_projection {β γ : ℝ} {n : ℕ}
    (hmn : HypercubeRamsey.S04.specialNum β γ n ≤ n)
    (v : CubeVertex n)
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)) :
    HypercubeRamsey.S04.clipped β γ n g j v =
      clippedBlockWeight (HypercubeRamsey.S04.gadgetPower β γ n)
        (HypercubeRamsey.S04.chunkLen β γ n)
        ((gadgetFirstBlocksEquiv
          (by simpa [HypercubeRamsey.S04.specialNum, Nat.mul_assoc] using hmn)
          (fun i => v i.1)) (g, j)) := by
  classical
  let S := HypercubeRamsey.S04.gadgetPower β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hset :
      trueCoordinatesEquiv
          ((gadgetFirstBlocksEquiv
            (by simpa [HypercubeRamsey.S04.specialNum, Nat.mul_assoc] using hmn)
            (fun i => v i.1)) (g, j)) =
        Finset.univ.filter (fun r : Fin ℓ =>
          v (Fin.castLE
            (by simpa [HypercubeRamsey.S04.specialNum, Nat.mul_assoc] using hmn)
            (gadgetChunkEquiv (HypercubeRamsey.S04.gadgetNum β γ n)
              (HypercubeRamsey.S04.chunkNum β γ n) ℓ ((g, j), r))) = true) := by
    ext r
    simp [trueCoordinatesEquiv, gadgetFirstBlocks_apply]
  unfold clippedBlockWeight
  simp only [HypercubeRamsey.S04.clipped]
  rw [chunkCount_eq_blockWeight hmn g j v, hset]

private theorem midpoint_cutoff_lt_square (S a : ℕ) (hS : 2 ≤ S) (ha : a < S) :
    a * S + S / 2 < S ^ 2 := by
  have hmul : a * S + S ≤ S * S := by
    calc
      a * S + S = (a + 1) * S := by rw [Nat.add_mul, one_mul]
      _ ≤ S * S := Nat.mul_le_mul_right S (Nat.succ_le_of_lt ha)
  have hdiv : S / 2 < S := Nat.div_lt_self (by omega) (by omega)
  have hlt : a * S + S / 2 < a * S + S := Nat.add_lt_add_left hdiv _
  exact lt_of_lt_of_le hlt (by simpa [pow_two] using hmul)

private theorem keyFiber_block_sets_fraction {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n)
    (S : ℕ) (hS : S = HypercubeRamsey.S04.gadgetPower β γ n)
    (hSlarge : 100 ≤ S)
    (hSeven : Even S) :
    ∀ (a : Fin S) (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
      (j : Fin (HypercubeRamsey.S04.chunkNum β γ n)),
      ((Finset.univ.filter fun f : Fin (HypercubeRamsey.S04.chunkLen β γ n) → Bool =>
        if j ∈ (κ g).2 then
          a.val * S + S / 2 < clippedBlockWeight S
            (HypercubeRamsey.S04.chunkLen β γ n) f
        else
          clippedBlockWeight S (HypercubeRamsey.S04.chunkLen β γ n) f ≤
            a.val * S + S / 2).card : ℝ) ≤
      (2 / 3) * (2 : ℝ) ^ HypercubeRamsey.S04.chunkLen β γ n := by
  intro a g j
  have htpos : 0 < a.val * S + S / 2 := by omega
  have htlt : a.val * S + S / 2 < S ^ 2 :=
    midpoint_cutoff_lt_square S a.val (by omega) a.isLt
  have hend := clipped_endpoint_counts S
    (HypercubeRamsey.S04.chunkLen β γ n) hSlarge hSeven
    (by rw [hS]; simp [HypercubeRamsey.S04.chunkLen,
      HypercubeRamsey.S04.chunkNum])
  have hside := clippedBlock_side_card_le S
    (HypercubeRamsey.S04.chunkLen β γ n)
    (a.val * S + S / 2) hend.1 hend.2 htpos htlt
  split_ifs with hj
  · simpa [hj] using hside.1
  · simpa [hj] using hside.2

private theorem keyFiber_constraint_assignment_card_le {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n)
    (hmn : HypercubeRamsey.S04.specialNum β γ n ≤ n)
    (S : ℕ) (hS : S = HypercubeRamsey.S04.gadgetPower β γ n)
    (hSlarge : 100 ≤ S) (hSeven : Even S) :
    ∀ (a : Fin (HypercubeRamsey.S04.gadgetNum β γ n) → Fin S),
      ((Finset.univ.filter fun z :
        (∀ i : {x : Fin n // x ∈ firstCoordinates n
          (HypercubeRamsey.S04.gadgetNum β γ n *
            HypercubeRamsey.S04.chunkNum β γ n *
            HypercubeRamsey.S04.chunkLen β γ n)}, Bool) =>
          ∀ b : Fin (HypercubeRamsey.S04.gadgetNum β γ n) ×
              Fin (HypercubeRamsey.S04.chunkNum β γ n),
            (if b.2 ∈ (κ b.1).2 then
              (a b.1).val * S + S / 2 <
                clippedBlockWeight S (HypercubeRamsey.S04.chunkLen β γ n)
                  ((gadgetFirstBlocksEquiv
                  (by simpa [HypercubeRamsey.S04.specialNum] using hmn)
                  z) b)
            else
              clippedBlockWeight S (HypercubeRamsey.S04.chunkLen β γ n)
                ((gadgetFirstBlocksEquiv
                (by simpa [HypercubeRamsey.S04.specialNum] using hmn)
                z) b) ≤ (a b.1).val * S + S / 2)).card : ℝ) ≤
        (2 / 3) ^ (HypercubeRamsey.S04.gadgetNum β γ n *
            HypercubeRamsey.S04.chunkNum β γ n) *
          (2 : ℝ) ^ HypercubeRamsey.S04.specialNum β γ n := by
  intro a
  classical
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hm : HypercubeRamsey.S04.specialNum β γ n = G * s * ℓ := by
    rfl
  have hmn' : G * s * ℓ ≤ n := by
    rw [← hm]
    exact hmn
  let B : (Fin G × Fin s) → Finset (Fin ℓ → Bool) := fun b =>
    Finset.univ.filter fun f =>
      if b.2 ∈ (κ b.1).2 then
        (a b.1).val * S + S / 2 < clippedBlockWeight S ℓ f
      else
        clippedBlockWeight S ℓ f ≤ (a b.1).val * S + S / 2
  let C : (∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool) → Prop := fun z =>
    ∀ b : Fin G × Fin s, (gadgetFirstBlocksEquiv
      hmn'
      z) b ∈ B b
  have hB : ∀ b, ((B b).card : ℝ) ≤ (2 / 3) * (2 : ℝ) ^ ℓ := by
    intro b
    simpa [B] using keyFiber_block_sets_fraction κ S hS hSlarge hSeven
      (a b.1) b.1 b.2
  have hcount := gadgetFirstBlock_constraint_count
    (G := G) (s := s) (ℓ := ℓ) (n := n)
    hmn' B
  have hfrac := block_constraint_fraction (gadgetChunkEquiv G s ℓ) B hB
  have hcount' : Fintype.card
      {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool // C z} =
      ∏ b : Fin G × Fin s, (B b).card := by
    exact hcount
  have hcountBlock := block_constraint_count (gadgetChunkEquiv G s ℓ) B
  have hcards : Fintype.card
      {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool // C z} =
      Fintype.card {f : Fin (G * s * ℓ) → Bool //
        ∀ b : Fin G × Fin s,
          (blockAssignmentsEquiv (gadgetChunkEquiv G s ℓ) f) b ∈ B b} := by
    rw [hcount', hcountBlock]
  have hC : (Fintype.card
      {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool // C z} : ℝ) ≤
      (2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ) := by
    rw [hcards]
    simpa [Fintype.card_fin] using hfrac
  have hFinset :
      (Finset.univ.filter fun z : ∀ i : {x : Fin n // x ∈ firstCoordinates n
        (G * s * ℓ)}, Bool => C z).card =
        Fintype.card {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool // C z} := by
    let F : Finset (∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool) :=
      Finset.univ.filter C
    have hmem (z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool) :
        z ∈ F ↔ C z := by simp [F]
    let e : {z // z ∈ F} ≃
        {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool // C z} := {
      toFun := fun z => ⟨z.1, (hmem z.1).mp z.2⟩
      invFun := fun z => ⟨z.1, (hmem z.1).mpr z.2⟩
      left_inv := by intro z; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl
    }
    calc
      (Finset.univ.filter C).card = F.card := by rfl
      _ = Fintype.card {z // z ∈ F} := (Fintype.card_coe F).symm
      _ = Fintype.card {z : ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)},
          Bool // C z} :=
        Fintype.card_congr e
  have hC' : ((Finset.univ.filter fun z :
      ∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool => C z).card : ℝ) ≤
      (2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ) := by
    simpa [hFinset] using hC
  rw [hm]
  simpa [C, B, G, s] using hC'

theorem log_power_le_chunk (S s : ℕ) (hS : 128 ≤ S)
    (hs : s = S - 1) :
    Real.log (S : ℝ) ≤ (s : ℝ) / 12 := by
  have hSpos : 0 < (S : ℝ) := by positivity
  have hSreal : 128 ≤ (S : ℝ) := by exact_mod_cast hS
  have hdivpos : 0 < (S : ℝ) / 128 := by positivity
  have hlogdiv := Real.log_le_sub_one_of_pos hdivpos
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hlog128 : Real.log (128 : ℝ) ≤ 7 := by
    rw [show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num, Real.log_pow]
    calc
      (7 : ℝ) * Real.log 2 ≤ 7 * 1 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
      _ = 7 := by ring
  have hmul : (S : ℝ) / 128 * 128 = (S : ℝ) := by field_simp
  have hlogmul : Real.log (S : ℝ) =
      Real.log ((S : ℝ) / 128) + Real.log (128 : ℝ) := by
    calc
      Real.log (S : ℝ) = Real.log ((S : ℝ) / 128 * 128) := by rw [hmul]
      _ = Real.log ((S : ℝ) / 128) + Real.log (128 : ℝ) :=
        Real.log_mul hdivpos.ne' (by norm_num : (128 : ℝ) ≠ 0)
  have hlogupper : Real.log (S : ℝ) ≤ (S : ℝ) / 128 + 6 := by
    rw [hlogmul]
    nlinarith
  have htarget : (S : ℝ) / 128 + 6 ≤ ((S : ℝ) - 1) / 12 := by
    nlinarith [hSreal]
  have hcastSub : ((S - 1 : ℕ) : ℝ) = (S : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ S)]
    norm_num
  have hsCast : (s : ℝ) = (S : ℝ) - 1 := by
    rw [hs, hcastSub]
  rw [hsCast]
  exact hlogupper.trans htarget

theorem keyFiber_all_leaf_constraints_card_le {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n)
    (hmn : HypercubeRamsey.S04.specialNum β γ n ≤ n)
    (S : ℕ) (hS : S = HypercubeRamsey.S04.gadgetPower β γ n)
    (hSlarge : 100 ≤ S) (hSeven : Even S) :
    ((Finset.univ.filter fun z :
        (∀ i : {x : Fin n // x ∈ firstCoordinates n
          (HypercubeRamsey.S04.gadgetNum β γ n *
            HypercubeRamsey.S04.chunkNum β γ n *
            HypercubeRamsey.S04.chunkLen β γ n)}, Bool) =>
        ∃ a : Fin (HypercubeRamsey.S04.gadgetNum β γ n) → Fin S,
          ∀ b : Fin (HypercubeRamsey.S04.gadgetNum β γ n) ×
              Fin (HypercubeRamsey.S04.chunkNum β γ n),
            if b.2 ∈ (κ b.1).2 then
              (a b.1).val * S + S / 2 < clippedBlockWeight S
                (HypercubeRamsey.S04.chunkLen β γ n)
                ((gadgetFirstBlocksEquiv
                  (by simpa [HypercubeRamsey.S04.specialNum] using hmn) z) b)
            else
              clippedBlockWeight S (HypercubeRamsey.S04.chunkLen β γ n)
                ((gadgetFirstBlocksEquiv
                  (by simpa [HypercubeRamsey.S04.specialNum] using hmn) z) b) ≤
                (a b.1).val * S + S / 2).card : ℝ) ≤
      (S : ℝ) ^ HypercubeRamsey.S04.gadgetNum β γ n *
        (2 / 3) ^ (HypercubeRamsey.S04.gadgetNum β γ n *
          HypercubeRamsey.S04.chunkNum β γ n) *
        (2 : ℝ) ^ HypercubeRamsey.S04.specialNum β γ n := by
  classical
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  let Leaves := (Fin G → Fin S)
  let Coord := (∀ i : {x : Fin n // x ∈ firstCoordinates n (G * s * ℓ)}, Bool)
  let C : Leaves → Coord → Prop := fun a z =>
    ∀ b : Fin G × Fin s,
      if b.2 ∈ (κ b.1).2 then
        (a b.1).val * S + S / 2 < clippedBlockWeight S ℓ
          ((gadgetFirstBlocksEquiv
            (by simpa [HypercubeRamsey.S04.specialNum] using hmn) z) b)
      else
        clippedBlockWeight S ℓ
          ((gadgetFirstBlocksEquiv
            (by simpa [HypercubeRamsey.S04.specialNum] using hmn) z) b) ≤
          (a b.1).val * S + S / 2
  let F : Leaves → Finset Coord := fun a => Finset.univ.filter (C a)
  have hmn' : G * s * ℓ ≤ n := by
    simpa [HypercubeRamsey.S04.specialNum, G, s, ℓ] using hmn
  have hF : ∀ a, ((F a).card : ℝ) ≤
      (2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ) := by
    intro a
    have h := keyFiber_constraint_assignment_card_le κ hmn S hS hSlarge hSeven a
    rw [show HypercubeRamsey.S04.specialNum β γ n = G * s * ℓ by rfl] at h
    simpa [F, C, G, s, ℓ] using h
  have hUnionNat := card_exists_finite_constraints_le_sum F
  have hUnion : (Finset.univ.filter fun z : Coord => ∃ a : Leaves, z ∈ F a).card ≤
      ∑ a : Leaves, (F a).card := by
    simpa [F, C, G, s, ℓ] using hUnionNat
  have hSum : (∑ a : Leaves, ((F a).card : ℝ)) ≤
      (Fintype.card Leaves : ℝ) *
        ((2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ)) := by
    calc
      (∑ a : Leaves, ((F a).card : ℝ)) ≤
          ∑ _a : Leaves, ((2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ)) :=
        Finset.sum_le_sum fun a _ => hF a
      _ = (Fintype.card Leaves : ℝ) *
          ((2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ)) := by simp
  have hCastUnion :
      ((Finset.univ.filter fun z : Coord => ∃ a : Leaves, z ∈ F a).card : ℝ) ≤
        (Fintype.card Leaves : ℝ) *
          ((2 / 3) ^ (G * s) * (2 : ℝ) ^ (G * s * ℓ)) := by
    calc
      ((Finset.univ.filter fun z : Coord => ∃ a : Leaves, z ∈ F a).card : ℝ) ≤
          ((∑ a : Leaves, (F a).card : ℕ) : ℝ) := by exact_mod_cast hUnion
      _ = ∑ a : Leaves, ((F a).card : ℝ) := by simp
      _ ≤ _ := hSum
  have hLeaves : Fintype.card Leaves = S ^ G := by
    simp [Leaves, G]
  have hset :
      (Finset.univ.filter fun z : Coord => ∃ a : Leaves, z ∈ F a) =
        (Finset.univ.filter fun z : Coord => ∃ a : Leaves, C a z) := by
    ext z
    simp [F]
  have hbound := hCastUnion
  rw [hset] at hbound
  have hspecial : HypercubeRamsey.S04.specialNum β γ n = G * s * ℓ := rfl
  simpa [C, hLeaves, hspecial, G, s, ℓ, Leaves, mul_assoc,
    Finset.mem_filter, Finset.mem_univ] using hbound

theorem keyFiber_key_satisfies_leaf_constraints {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n)
    (hmn : HypercubeRamsey.S04.specialNum β γ n ≤ n)
    (S : ℕ) (hS : S = HypercubeRamsey.S04.gadgetPower β γ n)
    (v : CubeVertex n) (hkey : HypercubeRamsey.S04.key β γ n v = κ) :
    ∃ a : Fin (HypercubeRamsey.S04.gadgetNum β γ n) → Fin S,
      ∀ b : Fin (HypercubeRamsey.S04.gadgetNum β γ n) ×
          Fin (HypercubeRamsey.S04.chunkNum β γ n),
        if b.2 ∈ (κ b.1).2 then
          (a b.1).val * S + S / 2 < clippedBlockWeight S
            (HypercubeRamsey.S04.chunkLen β γ n)
            ((gadgetFirstBlocksEquiv
              (by simpa [HypercubeRamsey.S04.specialNum] using hmn)
              (fun i => v i.1)) b)
        else
          clippedBlockWeight S (HypercubeRamsey.S04.chunkLen β γ n)
            ((gadgetFirstBlocksEquiv
              (by simpa [HypercubeRamsey.S04.specialNum] using hmn)
              (fun i => v i.1)) b) ≤ (a b.1).val * S + S / 2 := by
  classical
  let G := HypercubeRamsey.S04.gadgetNum β γ n
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hmn' : G * s * ℓ ≤ n := by
    simpa [HypercubeRamsey.S04.specialNum, G, s, ℓ] using hmn
  let a : Fin G → Fin S := fun g =>
    ⟨(HypercubeRamsey.S04.searchLeaf β γ n g v).1, by
      rw [hS]
      exact searchLeaf_first_lt_power g v⟩
  refine ⟨a, ?_⟩
  intro b
  have hside := key_output_side_constraint κ v hkey b.1 b.2
  have hthreshold : (a b.1).val * S + S / 2 =
      (HypercubeRamsey.S04.searchLeaf β γ n b.1 v).1 *
        HypercubeRamsey.S04.gadgetPower β γ n +
        HypercubeRamsey.S04.gadgetPower β γ n / 2 := by
    simp [a, hS]
  have hclip0 := clipped_eq_blockWeight_of_projection hmn v b.1 b.2
  have hclip : HypercubeRamsey.S04.clipped β γ n b.1 b.2 v =
      clippedBlockWeight S ℓ
        ((gadgetFirstBlocksEquiv hmn' (fun i => v i.1)) b) := by
    simpa [hS, ℓ] using hclip0
  by_cases hj : b.2 ∈ (κ b.1).2
  · simp only [hj, if_pos]
    rw [hthreshold, ← hclip]
    exact hside.1 hj
  · simp only [hj, if_neg]
    rw [← hclip, hthreshold]
    exact hside.2 hj

theorem evenRole_filter_card_eq_key_filter {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n) :
    (Finset.univ.filter fun a : EvenRole n =>
      HypercubeRamsey.S04.key β γ n a.1 = κ).card =
      ((HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
        HypercubeRamsey.S04.key β γ n v = κ).card := by
  classical
  let F : Finset (EvenRole n) := Finset.univ.filter fun a =>
    HypercubeRamsey.S04.key β γ n a.1 = κ
  let V : Finset (CubeVertex n) := (HypercubeRamsey.evenRoleSet n).filter fun v =>
    HypercubeRamsey.S04.key β γ n v = κ
  let e : {a : EvenRole n // a ∈ F} ≃ {v : CubeVertex n // v ∈ V} := {
    toFun := fun a => ⟨a.1.1, Finset.mem_filter.mpr
      ⟨by simpa [HypercubeRamsey.evenRoleSet] using a.1.2,
       (Finset.mem_filter.mp a.2).2⟩⟩
    invFun := fun v => ⟨⟨v.1, by
      simpa [HypercubeRamsey.evenRoleSet] using (Finset.mem_filter.mp v.2).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp v.2).2⟩⟩
    left_inv := by intro a; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro v; apply Subtype.ext; rfl
  }
  calc
    F.card = Fintype.card {a : EvenRole n // a ∈ F} := (Fintype.card_coe F).symm
    _ = Fintype.card {v : CubeVertex n // v ∈ V} := Fintype.card_congr e
    _ = V.card := Fintype.card_coe V

theorem oddRole_filter_card_eq_key_filter {β γ : ℝ} {n : ℕ}
    (κ : HypercubeRamsey.S04.Key β γ n) :
    (Finset.univ.filter fun u : OddRole n =>
      HypercubeRamsey.S04.key β γ n u.1 = κ).card =
      ((Finset.univ \ HypercubeRamsey.evenRoleSet n).filter fun v : CubeVertex n =>
        HypercubeRamsey.S04.key β γ n v = κ).card := by
  classical
  let F : Finset (OddRole n) := Finset.univ.filter fun u =>
    HypercubeRamsey.S04.key β γ n u.1 = κ
  let O : Finset (CubeVertex n) := Finset.univ \ HypercubeRamsey.evenRoleSet n
  let V : Finset (CubeVertex n) := O.filter fun v =>
    HypercubeRamsey.S04.key β γ n v = κ
  let e : {u : OddRole n // u ∈ F} ≃ {v : CubeVertex n // v ∈ V} := {
    toFun := fun u => ⟨u.1.1, Finset.mem_filter.mpr
      ⟨by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro he
        exact u.1.2 (by simpa [HypercubeRamsey.evenRoleSet] using
          (Finset.mem_filter.mp he).2),
       (Finset.mem_filter.mp u.2).2⟩⟩
    invFun := fun v => ⟨⟨v.1, by
      intro he
      have hEven : v.1 ∈ HypercubeRamsey.evenRoleSet n := by
        simp [HypercubeRamsey.evenRoleSet, he]
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp v.2).1).2 hEven⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp v.2).2⟩⟩
    left_inv := by intro u; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro v; apply Subtype.ext; rfl
  }
  calc
    F.card = Fintype.card {u : OddRole n // u ∈ F} := (Fintype.card_coe F).symm
    _ = Fintype.card {v : CubeVertex n // v ∈ V} := Fintype.card_congr e
    _ = V.card := Fintype.card_coe V

theorem pow_two_partition_mul (m n : ℕ) (hmn : m < n) :
    (2 : ℝ) ^ m * (2 : ℝ) ^ (n - m - 1) = (2 : ℝ) ^ (n - 1) := by
  rw [← pow_add]
  congr 1
  omega

private theorem countP_ofFn_sum {α : Type*} {n : ℕ} (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = ∑ i : Fin n, if p (f i) then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.countP_append, List.countP_singleton]
    rw [ih, Fin.sum_univ_castSucc]

private theorem countP_ofFn_card {n : ℕ} (f : Fin n → ℕ) (c : ℕ) :
    (List.ofFn f).countP (fun x => decide (x ≤ c)) =
      (Finset.univ.filter fun i : Fin n => f i ≤ c).card := by
  calc
    (List.ofFn f).countP (fun x => decide (x ≤ c)) =
        ∑ i : Fin n, if f i ≤ c then 1 else 0 := by
          simpa using countP_ofFn_sum f (fun x => decide (x ≤ c))
    _ = (Finset.univ.filter fun i : Fin n => f i ≤ c).card := by
      rw [Finset.card_filter]

private theorem mergeSortAt_mono {n : ℕ} (f g : Fin n → ℕ)
    (hfg : ∀ i, f i ≤ g i) (k : Fin n) :
    ((List.ofFn f).mergeSort (fun a b => decide (a ≤ b))).get
        ⟨k.val, by simp⟩ ≤
      ((List.ofFn g).mergeSort (fun a b => decide (a ≤ b))).get
        ⟨k.val, by simp⟩ := by
  classical
  let Lf := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  let Lg := (List.ofFn g).mergeSort (fun a b => decide (a ≤ b))
  have hlenf : Lf.length = n := by simp [Lf]
  have hLeng : Lg.length = n := by simp [Lg]
  let qf : Fin n → ℕ := fun i => Lf.get (Fin.cast hlenf.symm i)
  let qg : Fin n → ℕ := fun i => Lg.get (Fin.cast hLeng.symm i)
  have hqf : ∀ i : Fin n, qf i = Lf.get ⟨i.val, by simpa [Lf] using i.isLt⟩ := by
    intro i
    rfl
  have hqg : ∀ i : Fin n, qg i = Lg.get ⟨i.val, by simpa [Lg] using i.isLt⟩ := by
    intro i
    rfl
  have hmonf : Monotone qf := by
    have hs : Lf.SortedLE := by simpa [Lf] using
      (List.sortedLE_mergeSort (l := List.ofFn f))
    intro i j hij
    apply hs.monotone_get
    simpa [qf, Fin.val_cast] using hij
  have hmonG : Monotone qg := by
    have hs : Lg.SortedLE := by simpa [Lg] using
      (List.sortedLE_mergeSort (l := List.ofFn g))
    intro i j hij
    apply hs.monotone_get
    simpa [qg, Fin.val_cast] using hij
  have hOfFnF : List.ofFn qf = Lf := by
    change List.ofFn (fun i : Fin n => Lf.get (Fin.cast hlenf.symm i)) = Lf
    rw [← List.ofFn_congr hlenf (List.get Lf)]
    exact List.ofFn_get Lf
  have hOfFnG : List.ofFn qg = Lg := by
    change List.ofFn (fun i : Fin n => Lg.get (Fin.cast hLeng.symm i)) = Lg
    rw [← List.ofFn_congr hLeng (List.get Lg)]
    exact List.ofFn_get Lg
  by_contra hnot
  have hgt : qg k < qf k := Nat.lt_of_not_ge (by simpa [qf, qg, Lf, Lg] using hnot)
  let c := qg k
  let FF : Finset (Fin n) := Finset.univ.filter fun i => qf i ≤ c
  let FG : Finset (Fin n) := Finset.univ.filter fun i => qg i ≤ c
  have hFGprefix : Finset.Iic k ⊆ FG := by
    intro i hi
    have hik : i ≤ k := Finset.mem_Iic.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      dsimp [c]
      exact (hmonG hik).trans (Nat.le_refl _)
    ⟩
  have hFGcard : k.val + 1 ≤ FG.card := by
    calc
      k.val + 1 = (Finset.Iic k).card := by simp
      _ ≤ FG.card := Finset.card_le_card hFGprefix
  have hFGperm : FG.card = (List.ofFn g).countP (fun x => decide (x ≤ c)) := by
    calc
      FG.card = (List.ofFn qg).countP (fun x => decide (x ≤ c)) := by
        symm
        exact countP_ofFn_card qg c
      _ = Lg.countP (fun x => decide (x ≤ c)) := by rw [hOfFnG]
      _ = (List.ofFn g).countP (fun x => decide (x ≤ c)) := by
        exact (List.mergeSort_perm (List.ofFn g) (fun a b => decide (a ≤ b))).countP_eq _
  have hFFperm : FF.card = (List.ofFn f).countP (fun x => decide (x ≤ c)) := by
    calc
      FF.card = (List.ofFn qf).countP (fun x => decide (x ≤ c)) := by
        symm
        exact countP_ofFn_card qf c
      _ = Lf.countP (fun x => decide (x ≤ c)) := by rw [hOfFnF]
      _ = (List.ofFn f).countP (fun x => decide (x ≤ c)) := by
        exact (List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))).countP_eq _
  have hFFsubset : FF ⊆ (Finset.Iio k) := by
    intro i hi
    have hqi : qf i ≤ c := (Finset.mem_filter.mp hi).2
    apply Finset.mem_Iio.mpr
    by_contra hk
    have hki : k ≤ i := le_of_not_gt hk
    have hmono := hmonf hki
    dsimp [c] at hqi
    omega
  have hFFcard : FF.card ≤ k.val := by
    calc
      FF.card ≤ (Finset.Iio k).card := Finset.card_le_card hFFsubset
      _ = k.val := by simp
  have hinputSub : (Finset.univ.filter fun i : Fin n => g i ≤ c) ⊆
      (Finset.univ.filter fun i : Fin n => f i ≤ c) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hfg i).trans (Finset.mem_filter.mp hi).2⟩
  have hinputCard := Finset.card_le_card hinputSub
  have hinputCount : (List.ofFn g).countP (fun x => decide (x ≤ c)) ≤
      (List.ofFn f).countP (fun x => decide (x ≤ c)) := by
    calc
      (List.ofFn g).countP (fun x => decide (x ≤ c)) =
          (Finset.univ.filter fun i : Fin n => g i ≤ c).card := countP_ofFn_card g c
      _ ≤ (Finset.univ.filter fun i : Fin n => f i ≤ c).card := hinputCard
      _ = (List.ofFn f).countP (fun x => decide (x ≤ c)) := (countP_ofFn_card f c).symm
  have hFGleFF : FG.card ≤ FF.card := by
    calc
      FG.card = (List.ofFn g).countP (fun x => decide (x ≤ c)) := hFGperm
      _ ≤ (List.ofFn f).countP (fun x => decide (x ≤ c)) := hinputCount
      _ = FF.card := hFFperm.symm
  omega

private def mergeSortAt {n : ℕ} (f : Fin n → ℕ) (i : Fin n) : ℕ :=
  ((List.ofFn f).mergeSort (fun a b => decide (a ≤ b))).get ⟨i.val, by simp⟩

private theorem mergeSortAt_monotone {n : ℕ} (f : Fin n → ℕ) :
    Monotone (mergeSortAt f) := by
  classical
  let L := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  have hlen : L.length = n := by simp [L]
  let q : Fin n → ℕ := fun i => L.get (Fin.cast hlen.symm i)
  have hq : ∀ i : Fin n, q i = mergeSortAt f i := by intro i; rfl
  have hs : L.SortedLE := by
    simpa [L] using (List.sortedLE_mergeSort (l := List.ofFn f))
  have hqmon : Monotone q := by
    intro i j hij
    apply hs.monotone_get
    simpa [q, Fin.val_cast] using hij
  intro i j hij
  rw [← hq i, ← hq j]
  exact hqmon hij

private theorem mergeSort_mem_gap {n : ℕ} (f : Fin n → ℕ) (p q : Fin n)
    (hpq : q.val = p.val + 1) (x : ℕ) (hx : x ∈ List.ofFn f) :
    x ≤ mergeSortAt f p ∨ mergeSortAt f q ≤ x := by
  classical
  let L := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  have hlen : L.length = n := by simp [L]
  have hperm := List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))
  have hxsort : x ∈ L := hperm.mem_iff.mpr hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxsort
  let i' : Fin n := Fin.cast hlen i
  have hival : i'.val = i.val := by simp [i']
  have hiNat : i.val < n := by simpa [hlen] using i.isLt
  have hxi : mergeSortAt f i' = x := by
    dsimp [mergeSortAt, L, i']
    simpa using hi
  have hmon := mergeSortAt_monotone f
  by_cases hip : i' ≤ p
  · left
    calc
      x = mergeSortAt f i' := hxi.symm
      _ ≤ mergeSortAt f p := hmon hip
  · right
    have hnotVal : ¬ i'.val ≤ p.val := by
      intro hv
      exact hip (Fin.le_iff_val_le_val.mpr hv)
    have hqi : q.val ≤ i'.val := by omega
    have hqi' : q ≤ i' := Fin.le_iff_val_le_val.mpr hqi
    calc
      mergeSortAt f q ≤ mergeSortAt f i' := hmon hqi'
      _ = x := hxi

private theorem mergeSort_mem_extremes {n : ℕ} (f : Fin n → ℕ) (hn : 0 < n)
    (x : ℕ) (hx : x ∈ List.ofFn f) :
    mergeSortAt f ⟨0, hn⟩ ≤ x ∧
      x ≤ mergeSortAt f ⟨n - 1, by omega⟩ := by
  classical
  let L := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  have hlen : L.length = n := by simp [L]
  have hperm := List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))
  have hxsort : x ∈ L := hperm.mem_iff.mpr hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxsort
  let i' : Fin n := Fin.cast hlen i
  have hival : i'.val = i.val := by simp [i']
  have hiLt : i.val < n := by rw [← hlen]; exact i.isLt
  have hxi : mergeSortAt f i' = x := by
    dsimp [mergeSortAt, L, i']
    simpa using hi
  have hmon := mergeSortAt_monotone f
  have hiLast : i' ≤ (⟨n - 1, by omega⟩ : Fin n) := by
    apply Fin.le_iff_val_le_val.mpr
    rw [hival]
    exact Nat.le_sub_one_of_lt hiLt
  constructor
  · calc
      mergeSortAt f ⟨0, hn⟩ ≤ mergeSortAt f i' :=
        hmon (Fin.le_iff_val_le_val.mpr (by simp))
      _ = x := hxi
  · calc
      x = mergeSortAt f i' := hxi.symm
      _ ≤ mergeSortAt f ⟨n - 1, by omega⟩ :=
        hmon hiLast

private theorem sum_ofFn_eq {n : ℕ} (f : Fin n → ℕ) :
    (List.ofFn f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.sum_append, List.sum_singleton]
    rw [ih, Fin.sum_univ_castSucc]

private theorem list_sum_eq_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    l₁.sum = l₂.sum := by
  letI : LeftCommutative (fun a b : ℕ => a + b) := ⟨by intro a b c; omega⟩
  exact h.foldr_eq (f := fun a b => a + b) (b := 0)

private theorem mergeSort_sum_eq (l : List ℕ) :
    (l.mergeSort (fun a b => decide (a ≤ b))).sum = l.sum := by
  letI : LeftCommutative (fun a b : ℕ => a + b) := ⟨by intro a b c; omega⟩
  have h := (List.mergeSort_perm l (fun a b => decide (a ≤ b))).foldr_eq
    (f := fun a b => a + b) (b := 0)
  exact h

private theorem mergeSortAt_add_one {n : ℕ} (f : Fin n → ℕ) (k : Fin n) :
    mergeSortAt (fun i => f i + 1) k = mergeSortAt f k + 1 := by
  let l := List.ofFn f
  have hraw : l.map Nat.succ = List.ofFn (fun i : Fin n => f i + 1) := by
    simp [l, Nat.succ_eq_add_one]
    funext i
    simp [Nat.succ_eq_add_one]
  have hmap : (l.mergeSort (fun a b => decide (a ≤ b))).map Nat.succ =
      ((l.map Nat.succ).mergeSort (fun a b => decide (a ≤ b))) := by
    apply List.map_mergeSort
    intro a ha b hb
    simp
  have hsorted :
      (l.mergeSort (fun a b => decide (a ≤ b))).map Nat.succ =
        (List.ofFn (fun i : Fin n => f i + 1)).mergeSort
          (fun a b => decide (a ≤ b)) := by
    rw [← hraw]
    exact hmap
  have hget := congrArg (fun L : List ℕ => L.getD k.val 0) hsorted
  simpa [mergeSortAt, l, List.getD_map, List.getD_eq_get, Nat.succ_eq_add_one] using hget.symm

private theorem rankValue_succ_eq_mergeSortAt {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n)
    (t : Fin (HypercubeRamsey.S04.chunkNum β γ n)) :
    HypercubeRamsey.S04.rankValue β γ n g v (t.val + 1) =
      mergeSortAt (fun j : Fin (HypercubeRamsey.S04.chunkNum β γ n) =>
        HypercubeRamsey.S04.clipped β γ n g j v) t := by
  have hchunk : HypercubeRamsey.S04.chunkNum β γ n + 1 =
      HypercubeRamsey.S04.gadgetPower β γ n := by
    unfold HypercubeRamsey.S04.chunkNum
    have hpos := HypercubeRamsey.S04.gadgetPower_pos β γ n
    omega
  have hpos : t.val + 1 ≠ 0 := by omega
  have hlt : t.val + 1 < HypercubeRamsey.S04.gadgetPower β γ n := by
    have ht := t.isLt
    omega
  have hne : t.val + 1 ≠ HypercubeRamsey.S04.gadgetPower β γ n := by omega
  simp [HypercubeRamsey.S04.rankValue, hpos, hne,
    HypercubeRamsey.S04.sortedCounts, mergeSortAt]

private theorem mergeSort_one_change {n : ℕ} (f g : Fin n → ℕ)
    (hfg : ∀ i, f i ≤ g i) (hgf : ∀ i, g i ≤ f i + 1)
    (hsum : (∑ i : Fin n, f i) + 1 = ∑ i : Fin n, g i) :
    ∃ r : Fin n, mergeSortAt g r = mergeSortAt f r + 1 ∧
      ∀ t : Fin n, t ≠ r → mergeSortAt g t = mergeSortAt f t := by
  classical
  let Lf := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  let Lg := (List.ofFn g).mergeSort (fun a b => decide (a ≤ b))
  have hlenf : Lf.length = n := by simp [Lf]
  have hLeng : Lg.length = n := by simp [Lg]
  let qf : Fin n → ℕ := fun i => Lf.get (Fin.cast hlenf.symm i)
  let qg : Fin n → ℕ := fun i => Lg.get (Fin.cast hLeng.symm i)
  have hqf : ∀ i : Fin n, qf i = mergeSortAt f i := by intro i; rfl
  have hqg : ∀ i : Fin n, qg i = mergeSortAt g i := by intro i; rfl
  have hOfFnF : List.ofFn qf = Lf := by
    change List.ofFn (fun i : Fin n => Lf.get (Fin.cast hlenf.symm i)) = Lf
    rw [← List.ofFn_congr hlenf (List.get Lf)]
    exact List.ofFn_get Lf
  have hOfFnG : List.ofFn qg = Lg := by
    change List.ofFn (fun i : Fin n => Lg.get (Fin.cast hLeng.symm i)) = Lg
    rw [← List.ofFn_congr hLeng (List.get Lg)]
    exact List.ofFn_get Lg
  have hlow : ∀ i, qf i ≤ qg i := by
    intro i
    simpa [qf, qg, Lf, Lg, mergeSortAt] using mergeSortAt_mono f g hfg i
  have hhigh : ∀ i, qg i ≤ qf i + 1 := by
    intro i
    have h := mergeSortAt_mono g (fun j => f j + 1) hgf i
    have h' : mergeSortAt g i ≤ mergeSortAt (fun j => f j + 1) i := by
      simpa [mergeSortAt] using h
    rw [mergeSortAt_add_one] at h'
    rw [hqg i, hqf i]
    exact h'
  have hsumf : (∑ i : Fin n, qf i) = ∑ i, f i := by
    calc
      (∑ i : Fin n, qf i) = (List.ofFn qf).sum := (sum_ofFn_eq qf).symm
      _ = Lf.sum := by rw [hOfFnF]
      _ = (List.ofFn f).sum := mergeSort_sum_eq (List.ofFn f)
      _ = ∑ i, f i := sum_ofFn_eq f
  have hsumg : (∑ i : Fin n, qg i) = ∑ i, g i := by
    calc
      (∑ i : Fin n, qg i) = (List.ofFn qg).sum := (sum_ofFn_eq qg).symm
      _ = Lg.sum := by rw [hOfFnG]
      _ = (List.ofFn g).sum := mergeSort_sum_eq (List.ofFn g)
      _ = ∑ i, g i := sum_ofFn_eq g
  have hqsum : (∑ i : Fin n, qf i) + 1 = ∑ i : Fin n, qg i := by
    rw [hsumf, hsumg]
    exact hsum
  have hpoint : ∀ i, qg i = qf i + if qf i < qg i then 1 else 0 := by
    intro i
    have hl := hlow i
    have hh := hhigh i
    by_cases h : qf i < qg i
    · have h' : qg i = qf i + 1 := by omega
      simp [h, h']
    · have h' : qg i = qf i := by omega
      simp [h, h']
  have hsumPoint : (∑ i : Fin n, qg i) =
      (∑ i : Fin n, qf i) + ∑ i : Fin n, if qf i < qg i then 1 else 0 := by
    calc
      (∑ i : Fin n, qg i) =
          ∑ i : Fin n, (qf i + if qf i < qg i then 1 else 0) :=
            Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = (∑ i : Fin n, qf i) + ∑ i : Fin n, if qf i < qg i then 1 else 0 :=
            Finset.sum_add_distrib
  have hdiffsum : (∑ i : Fin n, if qf i < qg i then 1 else 0) = 1 := by
    omega
  let D : Finset (Fin n) := Finset.univ.filter fun i => qf i < qg i
  have hDcard : D.card = 1 := by
    simpa [D] using hdiffsum
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hDcard
  have hrD : r ∈ D := by rw [hr]; simp
  have hrrank : qg r = qf r + 1 := by
    have hlt := (Finset.mem_filter.mp hrD).2
    have hl := hlow r
    have hh := hhigh r
    omega
  refine ⟨r, ?_, ?_⟩
  · simpa [hqf r, hqg r] using hrrank
  · intro t htr
    have htD : t ∉ D := by rw [hr]; simp [htr]
    have hnotlt : ¬ qf t < qg t := by simpa [D] using htD
    have hl := hlow t
    have hh := hhigh t
    have hEq : qg t = qf t := by omega
    simpa [hqf t, hqg t] using hEq

private theorem mergeSort_sum_sq {n : ℕ} (f : Fin n → ℕ) :
    (∑ i : Fin n, (mergeSortAt f i) ^ 2) = ∑ i : Fin n, (f i) ^ 2 := by
  classical
  let L := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  have hlen : L.length = n := by simp [L]
  let q : Fin n → ℕ := fun i => L.get (Fin.cast hlen.symm i)
  have hOfFn : List.ofFn q = L := by
    change List.ofFn (fun i : Fin n => L.get (Fin.cast hlen.symm i)) = L
    rw [← List.ofFn_congr hlen (List.get L)]
    exact List.ofFn_get L
  have hq : ∀ i : Fin n, q i = mergeSortAt f i := by intro i; rfl
  calc
    (∑ i : Fin n, (mergeSortAt f i) ^ 2) = ∑ i : Fin n, (q i) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [hq])
    _ = (List.ofFn (fun i : Fin n => (q i) ^ 2)).sum := (sum_ofFn_eq _).symm
    _ = ((List.ofFn q).map fun x : ℕ => x ^ 2).sum := by
      exact congrArg List.sum (List.ofFn_comp' q (fun x : ℕ => x ^ 2))
    _ = ((L.map fun x : ℕ => x ^ 2)).sum := by rw [hOfFn]
    _ = (((List.ofFn f).map fun x : ℕ => x ^ 2)).sum := by
      apply list_sum_eq_of_perm
      exact (List.mergeSort_perm (List.ofFn f) (fun a b => decide (a ≤ b))).map
        (fun x : ℕ => x ^ 2)
    _ = ∑ i : Fin n, (f i) ^ 2 := by simp [List.map_ofFn, sum_ofFn_eq]

private theorem mergeSort_one_change_at {n : ℕ} (f g : Fin n → ℕ) (j : Fin n)
    (hfg : ∀ i, f i ≤ g i) (hgf : ∀ i, g i ≤ f i + 1)
    (hsum : (∑ i : Fin n, f i) + 1 = ∑ i : Fin n, g i)
    (hcoord : g j = f j + 1) (hother : ∀ i, i ≠ j → g i = f i) :
    ∃ r : Fin n, mergeSortAt f r = f j ∧
      mergeSortAt g r = g j ∧
      ∀ t : Fin n, t ≠ r → mergeSortAt g t = mergeSortAt f t := by
  classical
  obtain ⟨r, hrank, hrest⟩ := mergeSort_one_change f g hfg hgf hsum
  have hinputSq : (∑ i : Fin n, (f i) ^ 2) + (2 * f j + 1) =
      ∑ i : Fin n, (g i) ^ 2 := by
    have hpoint : ∀ i : Fin n, (g i) ^ 2 = (f i) ^ 2 +
        if i = j then 2 * f j + 1 else 0 := by
      intro i
      by_cases hij : i = j
      · subst i
        rw [hcoord]
        simp
        ring
      · rw [hother i hij]
        simp [hij]
    calc
      _ = (∑ i : Fin n, (f i) ^ 2) +
          ∑ i : Fin n, (if i = j then 2 * f j + 1 else 0) := by simp
      _ = ∑ i : Fin n, ((f i) ^ 2 + if i = j then 2 * f j + 1 else 0) :=
        Finset.sum_add_distrib.symm
      _ = ∑ i : Fin n, (g i) ^ 2 :=
        Finset.sum_congr rfl (fun i _ => (hpoint i).symm)
  have hsortedSq :
      (∑ i : Fin n, (mergeSortAt g i) ^ 2) =
        (∑ i : Fin n, (mergeSortAt f i) ^ 2) + (2 * mergeSortAt f r + 1) := by
    have hpoint : ∀ i : Fin n, (mergeSortAt g i) ^ 2 =
        (mergeSortAt f i) ^ 2 + if i = r then 2 * mergeSortAt f r + 1 else 0 := by
      intro i
      by_cases hir : i = r
      · subst i
        rw [hrank]
        simp
        ring
      · rw [hrest i hir]
        simp [hir]
    calc
      _ = ∑ i : Fin n,
          ((mergeSortAt f i) ^ 2 + if i = r then 2 * mergeSortAt f r + 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => hpoint i)
      _ = (∑ i : Fin n, (mergeSortAt f i) ^ 2) +
          ∑ i : Fin n, (if i = r then 2 * mergeSortAt f r + 1 else 0) :=
        Finset.sum_add_distrib
      _ = (∑ i : Fin n, (mergeSortAt f i) ^ 2) + (2 * mergeSortAt f r + 1) := by simp
  have hcompare : (∑ i : Fin n, (f i) ^ 2) + (2 * f j + 1) =
      (∑ i : Fin n, (f i) ^ 2) + (2 * mergeSortAt f r + 1) := by
    calc
      _ = (∑ i : Fin n, (g i) ^ 2) := hinputSq
      _ = (∑ i : Fin n, (mergeSortAt g i) ^ 2) := (mergeSort_sum_sq g).symm
      _ = (∑ i : Fin n, (mergeSortAt f i) ^ 2) + (2 * mergeSortAt f r + 1) := hsortedSq
      _ = (∑ i : Fin n, (f i) ^ 2) + (2 * mergeSortAt f r + 1) := by
        rw [mergeSort_sum_sq f]
  have hvalue : mergeSortAt f r = f j := by omega
  exact ⟨r, hvalue, by rw [hrank, hvalue, hcoord], hrest⟩

private theorem mergeSortList_eq_of_at_eq {n : ℕ} (f g : Fin n → ℕ)
    (h : ∀ i, mergeSortAt f i = mergeSortAt g i) :
    (List.ofFn f).mergeSort (fun a b => decide (a ≤ b)) =
      (List.ofFn g).mergeSort (fun a b => decide (a ≤ b)) := by
  classical
  let Lf := (List.ofFn f).mergeSort (fun a b => decide (a ≤ b))
  let Lg := (List.ofFn g).mergeSort (fun a b => decide (a ≤ b))
  have hlenf : Lf.length = n := by simp [Lf]
  have hLeng : Lg.length = n := by simp [Lg]
  let qf : Fin n → ℕ := fun i => Lf.get (Fin.cast hlenf.symm i)
  let qg : Fin n → ℕ := fun i => Lg.get (Fin.cast hLeng.symm i)
  have hqf : ∀ i : Fin n, qf i = mergeSortAt f i := by intro i; rfl
  have hqg : ∀ i : Fin n, qg i = mergeSortAt g i := by intro i; rfl
  have hOfFnF : List.ofFn qf = Lf := by
    change List.ofFn (fun i : Fin n => Lf.get (Fin.cast hlenf.symm i)) = Lf
    rw [← List.ofFn_congr hlenf (List.get Lf)]
    exact List.ofFn_get Lf
  have hOfFnG : List.ofFn qg = Lg := by
    change List.ofFn (fun i : Fin n => Lg.get (Fin.cast hLeng.symm i)) = Lg
    rw [← List.ofFn_congr hLeng (List.get Lg)]
    exact List.ofFn_get Lg
  have hq : qf = qg := by
    funext i
    rw [hqf i, hqg i]
    exact h i
  calc
    Lf = List.ofFn qf := hOfFnF.symm
    _ = List.ofFn qg := congrArg List.ofFn hq
    _ = Lg := hOfFnG

private theorem searchLeaf_eq_of_rank_profile {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v w : CubeVertex n)
    (hprofile : ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      mergeSortAt (fun k => HypercubeRamsey.S04.clipped β γ n g k v) j =
        mergeSortAt (fun k => HypercubeRamsey.S04.clipped β γ n g k w) j) :
    HypercubeRamsey.S04.searchLeaf β γ n g v =
      HypercubeRamsey.S04.searchLeaf β γ n g w := by
  classical
  have hsorted := mergeSortList_eq_of_at_eq
    (fun j : Fin (HypercubeRamsey.S04.chunkNum β γ n) =>
      HypercubeRamsey.S04.clipped β γ n g j v)
    (fun j : Fin (HypercubeRamsey.S04.chunkNum β γ n) =>
      HypercubeRamsey.S04.clipped β γ n g j w) hprofile
  have hrv : ∀ t, HypercubeRamsey.S04.rankValue β γ n g v t =
      HypercubeRamsey.S04.rankValue β γ n g w t := by
    intro t
    simp [HypercubeRamsey.S04.rankValue,
      HypercubeRamsey.S04.sortedCounts, hsorted]
  have hstep : ∀ ab,
      HypercubeRamsey.S04.searchStep β γ n g v ab =
        HypercubeRamsey.S04.searchStep β γ n g w ab := by
    intro ab
    simp [HypercubeRamsey.S04.searchStep, hrv]
  have hfold (L : List ℕ) (ab : ℕ × ℕ) :
      List.foldl (fun st _ => HypercubeRamsey.S04.searchStep β γ n g v st) ab L =
        List.foldl (fun st _ => HypercubeRamsey.S04.searchStep β γ n g w st) ab L := by
    induction L generalizing ab with
    | nil => rfl
    | cons t L ih => simp [List.foldl_cons, hstep, ih]
  unfold HypercubeRamsey.S04.searchLeaf
  exact hfold _ _

private def binarySearchMid (ab : ℕ × ℕ) : ℕ := (ab.1 + ab.2) / 2

private def binarySearchStepR (S : ℕ) (R : ℕ → ℕ) (ab : ℕ × ℕ) : ℕ × ℕ :=
  if binarySearchMid ab * S ≤ R (binarySearchMid ab) then
    (ab.1, binarySearchMid ab) else (binarySearchMid ab, ab.2)

private def binarySearchRun (S : ℕ) (R : ℕ → ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, ab => ab
  | k + 1, ab => binarySearchStepR S R (binarySearchRun S R k ab)

private def binarySearchPath (S : ℕ) (R : ℕ → ℕ) : ℕ → ℕ × ℕ → List ℕ
  | 0, _ => []
  | k + 1, ab => binarySearchPath S R k ab ++
      [binarySearchMid (binarySearchRun S R k ab)]

private theorem foldl_range_binarySearchRun (S : ℕ) (R : ℕ → ℕ) (e : ℕ)
    (ab : ℕ × ℕ) :
    (List.range e).foldl (fun st _ => binarySearchStepR S R st) ab =
      binarySearchRun S R e ab := by
  induction e generalizing ab with
  | zero => rfl
  | succ e ih =>
    rw [List.range_succ, List.foldl_append]
    simp [List.foldl_cons, List.foldl_nil, ih, binarySearchRun]

private theorem binarySearchRun_eq_of_eq_on_path (S : ℕ) (R R' : ℕ → ℕ)
    (e : ℕ) (ab : ℕ × ℕ)
    (h : ∀ t ∈ binarySearchPath S R e ab, R t = R' t) :
    binarySearchRun S R e ab = binarySearchRun S R' e ab := by
  induction e generalizing ab with
  | zero => rfl
  | succ e ih =>
    have hprefix : ∀ t ∈ binarySearchPath S R e ab, R t = R' t := by
      intro t ht
      apply h t
      change t ∈ binarySearchPath S R e ab ++ _
      exact List.mem_append_left _ ht
    have hrun := ih ab hprefix
    have hmid : binarySearchMid (binarySearchRun S R e ab) =
        binarySearchMid (binarySearchRun S R' e ab) := by rw [hrun]
    have hlastmem : binarySearchMid (binarySearchRun S R e ab) ∈
        binarySearchPath S R (e + 1) ab := by simp [binarySearchPath]
    have hvalue := h _ hlastmem
    simp only [binarySearchRun]
    rw [hrun]
    simp only [binarySearchStepR]
    rw [← hmid]
    simp [hvalue]

private theorem binarySearchRun_endpoint_invariant (S e : ℕ) (R : ℕ → ℕ)
    (hS : S = 2 ^ e) (hzero : R 0 = 0) (hfinal : R S = S * S) :
    ∀ k ≤ e,
      (binarySearchRun S R k (0, S)).1 ≤ (binarySearchRun S R k (0, S)).2 ∧
      (binarySearchRun S R k (0, S)).2 =
        (binarySearchRun S R k (0, S)).1 + 2 ^ (e - k) ∧
      (binarySearchRun S R k (0, S)).2 ≤ S ∧
      R (binarySearchRun S R k (0, S)).1 ≤
        (binarySearchRun S R k (0, S)).1 * S ∧
      (binarySearchRun S R k (0, S)).2 * S ≤
        R (binarySearchRun S R k (0, S)).2 := by
  intro k
  induction k with
  | zero =>
    intro hk
    simp only [binarySearchRun]
    refine ⟨by omega, ?_, by omega, ?_, ?_⟩
    · simpa using hS
    · simpa using hzero
    · exact le_of_eq hfinal.symm
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    let ab := binarySearchRun S R k (0, S)
    have hab : ab.1 ≤ ab.2 := by simpa [ab] using hprev.1
    have hwidthPrev : ab.2 = ab.1 + 2 ^ (e - k) := by
      simpa [ab] using hprev.2.1
    have habUpper : ab.2 ≤ S := by simpa [ab] using hprev.2.2.1
    have hlo : R ab.1 ≤ ab.1 * S := by simpa [ab] using hprev.2.2.2.1
    have hhi : ab.2 * S ≤ R ab.2 := by simpa [ab] using hprev.2.2.2.2
    have hlen : e - k = (e - (k + 1)) + 1 := by omega
    let half := 2 ^ (e - (k + 1))
    have hpow : 2 ^ (e - k) = 2 * half := by
      rw [hlen, pow_succ]
      dsimp [half]
      omega
    have hwidth : ab.2 = ab.1 + 2 * half := by
      rw [hwidthPrev, hpow]
    have hhalf : 0 < half := by positivity
    let m := binarySearchMid ab
    have hmid : m = ab.1 + half := by
      dsimp [m, binarySearchMid]
      omega
    by_cases hc : m * S ≤ R m
    · have hrun : binarySearchRun S R (k + 1) (0, S) = (ab.1, m) := by
        simp only [binarySearchRun]
        change binarySearchStepR S R ab = (ab.1, m)
        unfold binarySearchStepR
        simp [m, hc]
      rw [hrun]
      simp only [Prod.fst, Prod.snd]
      refine ⟨?_, ?_, ?_, hlo, hc⟩
      · omega
      · simpa [half] using hmid
      · have hmle : m ≤ ab.2 := by rw [hmid, hwidth]; omega
        exact hmle.trans habUpper
    · have hc' : R m ≤ m * S := Nat.le_of_lt (lt_of_not_ge hc)
      have hrun : binarySearchRun S R (k + 1) (0, S) = (m, ab.2) := by
        simp only [binarySearchRun]
        change binarySearchStepR S R ab = (m, ab.2)
        unfold binarySearchStepR
        simp [m, hc]
      rw [hrun]
      simp only [Prod.fst, Prod.snd]
      refine ⟨?_, ?_, habUpper, hc', hhi⟩
      · omega
      · rw [hwidth, hmid]
        simp [half]
        omega

private theorem gadgetSearchLeaf_spec {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) :
    let S := HypercubeRamsey.S04.gadgetPower β γ n
    let ab := HypercubeRamsey.S04.searchLeaf β γ n g v
    ab.2 = ab.1 + 1 ∧
      ab.2 ≤ S ∧
      HypercubeRamsey.S04.rankValue β γ n g v ab.1 ≤ ab.1 * S ∧
      ab.2 * S ≤ HypercubeRamsey.S04.rankValue β γ n g v ab.2 := by
  classical
  let S := HypercubeRamsey.S04.gadgetPower β γ n
  let e := max 1 (⌈Real.log ((n : ℝ) ^ (2 * HypercubeRamsey.omega4 β γ)) /
    Real.log 2⌉₊)
  let R := HypercubeRamsey.S04.rankValue β γ n g v
  let ab := HypercubeRamsey.S04.searchLeaf β γ n g v
  have hS : S = 2 ^ e := by
    rfl
  have he : Nat.log2 S = e := by rw [hS, Nat.log2_two_pow]
  have hzero : R 0 = 0 := by simp [R, HypercubeRamsey.S04.rankValue]
  have hSpos : 0 < S := by
    exact HypercubeRamsey.S04.gadgetPower_pos β γ n
  have hfinal : R S = S * S := by
    simp [R, S, HypercubeRamsey.S04.rankValue, hSpos.ne', pow_two]
  have hfold : ab = binarySearchRun S R e (0, S) := by
    dsimp [ab, HypercubeRamsey.S04.searchLeaf]
    rw [he]
    change (List.range e).foldl (fun st _ => binarySearchStepR S R st) (0, S) = _
    exact foldl_range_binarySearchRun S R e (0, S)
  have hspec := binarySearchRun_endpoint_invariant S e R hS hzero hfinal e (Nat.le_refl _)
  rcases hspec with ⟨hle, hwidth, habUpper, hlo, hhi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [ab, hfold, S] using hwidth
  · simpa [ab, hfold, S] using habUpper
  · simpa [ab, R, hfold, S] using hlo
  · simpa [ab, R, hfold, S] using hhi

private theorem clipped_gap_of_search {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n)
    (hS : 4 ≤ HypercubeRamsey.S04.gadgetPower β γ n) :
    ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      HypercubeRamsey.S04.clipped β γ n g j v ≤
          (HypercubeRamsey.S04.searchLeaf β γ n g v).1 *
            HypercubeRamsey.S04.gadgetPower β γ n ∨
        (HypercubeRamsey.S04.searchLeaf β γ n g v).2 *
            HypercubeRamsey.S04.gadgetPower β γ n ≤
          HypercubeRamsey.S04.clipped β γ n g j v := by
  classical
  let S := HypercubeRamsey.S04.gadgetPower β γ n
  let ab := HypercubeRamsey.S04.searchLeaf β γ n g v
  let f : Fin (HypercubeRamsey.S04.chunkNum β γ n) → ℕ :=
    fun j => HypercubeRamsey.S04.clipped β γ n g j v
  have hspec : ab.2 = ab.1 + 1 ∧ ab.2 ≤ S ∧
      HypercubeRamsey.S04.rankValue β γ n g v ab.1 ≤ ab.1 * S ∧
      ab.2 * S ≤ HypercubeRamsey.S04.rankValue β γ n g v ab.2 := by
    simpa [ab, S] using gadgetSearchLeaf_spec g v
  have hchunk : HypercubeRamsey.S04.chunkNum β γ n + 1 = S := by
    unfold HypercubeRamsey.S04.chunkNum
    have hpos := HypercubeRamsey.S04.gadgetPower_pos β γ n
    omega
  have hn : 0 < HypercubeRamsey.S04.chunkNum β γ n := by omega
  intro j
  change f j ≤ ab.1 * S ∨ ab.2 * S ≤ f j
  have hxmem : f j ∈ List.ofFn f := List.mem_ofFn.mpr ⟨j, rfl⟩
  by_cases hzero : ab.1 = 0
  · have hfirstRank : HypercubeRamsey.S04.rankValue β γ n g v 1 =
        mergeSortAt f ⟨0, hn⟩ := by
      simpa [f] using rankValue_succ_eq_mergeSortAt g v ⟨0, hn⟩
    have hfirst : S ≤ mergeSortAt f ⟨0, hn⟩ := by
      have hb : ab.2 = 1 := by omega
      simpa [hzero, hb, hfirstRank] using hspec.2.2.2
    have hmin := mergeSort_mem_extremes f hn (f j) hxmem
    right
    have hb : ab.2 = 1 := by omega
    rw [hb]
    simpa using hfirst.trans hmin.1
  · by_cases htop : ab.2 = S
    · have haPos : 0 < ab.1 := Nat.pos_of_ne_zero hzero
      let p : Fin (HypercubeRamsey.S04.chunkNum β γ n) := ⟨ab.1 - 1, by omega⟩
      have hpVal : p.val + 1 = ab.1 := by dsimp [p]; omega
      have hlastRank : HypercubeRamsey.S04.rankValue β γ n g v ab.1 =
          mergeSortAt f p := by
        have h := rankValue_succ_eq_mergeSortAt g v p
        rw [hpVal] at h
        simpa [f] using h
      have hlastFin : p = ⟨HypercubeRamsey.S04.chunkNum β γ n - 1, by omega⟩ := by
        apply Fin.ext
        dsimp [p]
        omega
      have hmax := mergeSort_mem_extremes f hn (f j) hxmem
      have hmax' : f j ≤ mergeSortAt f p := by
        simpa [hlastFin] using hmax.2
      left
      calc
        f j ≤ mergeSortAt f p := hmax'
        _ = HypercubeRamsey.S04.rankValue β γ n g v ab.1 := hlastRank.symm
        _ ≤ ab.1 * S := hspec.2.2.1
    · have ha : ab.1 < HypercubeRamsey.S04.chunkNum β γ n := by
        have hstrict : ab.2 < S := lt_of_le_of_ne hspec.2.1 htop
        omega
      let p : Fin (HypercubeRamsey.S04.chunkNum β γ n) := ⟨ab.1 - 1, by omega⟩
      let q : Fin (HypercubeRamsey.S04.chunkNum β γ n) := ⟨ab.1, ha⟩
      have hpVal : p.val + 1 = ab.1 := by dsimp [p]; omega
      have hqVal : q.val + 1 = ab.2 := by dsimp [q]; omega
      have hpRank : HypercubeRamsey.S04.rankValue β γ n g v ab.1 =
          mergeSortAt f p := by
        have h := rankValue_succ_eq_mergeSortAt g v p
        rw [hpVal] at h
        simpa [f] using h
      have hqRank : HypercubeRamsey.S04.rankValue β γ n g v ab.2 =
          mergeSortAt f q := by
        have h := rankValue_succ_eq_mergeSortAt g v q
        rw [hqVal] at h
        simpa [f] using h
      have hpq : q.val = p.val + 1 := by dsimp [p, q]; omega
      rcases mergeSort_mem_gap f p q hpq (f j) hxmem with hlow | hhigh
      · left
        calc
          f j ≤ mergeSortAt f p := hlow
          _ = HypercubeRamsey.S04.rankValue β γ n g v ab.1 := hpRank.symm
          _ ≤ ab.1 * S := hspec.2.2.1
      · right
        calc
          ab.2 * S ≤ HypercubeRamsey.S04.rankValue β γ n g v ab.2 := hspec.2.2.2
          _ = mergeSortAt f q := hqRank
          _ ≤ f j := hhigh

private theorem side_stable_of_gap (S a x y : ℕ) (hS : 4 ≤ S)
    (hgap : x ≤ a * S ∨ (a + 1) * S ≤ x)
    (hdelta : y ≤ x + 1 ∧ x ≤ y + 1) :
    (a * S + S / 2 < x) ↔ (a * S + S / 2 < y) := by
  have hlowMid : a * S + 1 ≤ a * S + S / 2 := by omega
  have hhighMid : a * S + S / 2 + 1 ≤ a * S + S := by omega
  have hscale : (a + 1) * S = a * S + S := by
    rw [Nat.add_mul]
    simp
  rcases hgap with hlow | hhigh
  · have hxnot : ¬ a * S + S / 2 < x := by omega
    have hynot : ¬ a * S + S / 2 < y := by omega
    constructor <;> intro h <;> omega
  · have hbase : a * S + S ≤ x := by rw [← hscale]; exact hhigh
    have hx : a * S + S / 2 < x := by omega
    have hy : a * S + S / 2 < y := by omega
    exact ⟨fun _ => hy, fun _ => hx⟩

private theorem mergeSortNat_eq_of_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    l₁.mergeSort (fun a b => decide (a ≤ b)) =
      l₂.mergeSort (fun a b => decide (a ≤ b)) := by
  let r : ℕ → ℕ → Prop := (· ≤ ·)
  let cmp : ℕ → ℕ → Bool := fun a b => decide (r a b)
  have hp : List.Perm (l₁.mergeSort cmp) (l₂.mergeSort cmp) := by
    exact (List.mergeSort_perm l₁ cmp).trans
      (h.trans (List.mergeSort_perm l₂ cmp).symm)
  have hpair₁ : (l₁.mergeSort cmp).Pairwise r := by
    simpa [cmp, r] using List.pairwise_mergeSort' r l₁
  have hpair₂ : (l₂.mergeSort cmp).Pairwise r := by
    simpa [cmp, r] using List.pairwise_mergeSort' r l₂
  exact hp.eq_of_pairwise' hpair₁ hpair₂

private theorem gadgetOut_eq_of_leaf_and_side {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v w : CubeVertex n)
    (hleaf : HypercubeRamsey.S04.searchLeaf β γ n g v =
      HypercubeRamsey.S04.searchLeaf β γ n g w)
    (hside : ∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      ((HypercubeRamsey.S04.searchLeaf β γ n g v).1 *
          HypercubeRamsey.S04.gadgetPower β γ n +
          HypercubeRamsey.S04.gadgetPower β γ n / 2 <
        HypercubeRamsey.S04.clipped β γ n g j v) ↔
      ((HypercubeRamsey.S04.searchLeaf β γ n g w).1 *
          HypercubeRamsey.S04.gadgetPower β γ n +
          HypercubeRamsey.S04.gadgetPower β γ n / 2 <
        HypercubeRamsey.S04.clipped β γ n g j w)) :
    HypercubeRamsey.S04.gadgetOut β γ n g v =
      HypercubeRamsey.S04.gadgetOut β γ n g w := by
  classical
  have hside' := hside
  rw [hleaf] at hside'
  unfold HypercubeRamsey.S04.gadgetOut
  rw [hleaf]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hside' j

private theorem gadgetOut_flip_eq_of_leaf {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) (i : Fin n)
    (hleaf : HypercubeRamsey.S04.searchLeaf β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.searchLeaf β γ n g v)
    (hS : 4 ≤ HypercubeRamsey.S04.gadgetPower β γ n) :
    HypercubeRamsey.S04.gadgetOut β γ n g (HypercubeRamsey.cubeFlip v i) =
      HypercubeRamsey.S04.gadgetOut β γ n g v := by
  classical
  let S := HypercubeRamsey.S04.gadgetPower β γ n
  have hgap := clipped_gap_of_search g v hS
  have hwidth : (HypercubeRamsey.S04.searchLeaf β γ n g v).2 =
      (HypercubeRamsey.S04.searchLeaf β γ n g v).1 + 1 := by
    simpa using (gadgetSearchLeaf_spec g v).1
  apply Eq.symm
  apply gadgetOut_eq_of_leaf_and_side g v (HypercubeRamsey.cubeFlip v i) hleaf.symm
  intro j
  have hdelta :
      (HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) ≤
          HypercubeRamsey.S04.clipped β γ n g j v + 1) ∧
        (HypercubeRamsey.S04.clipped β γ n g j v ≤
          HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) + 1) := by
    by_cases hj : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g j
    · exact clipped_flip_delta g j v i hj
    · have heq := chunkCount_flip_eq g j v i hj
      simp [HypercubeRamsey.S04.clipped, heq]
  have hstable := side_stable_of_gap S
    (HypercubeRamsey.S04.searchLeaf β γ n g v).1
    (HypercubeRamsey.S04.clipped β γ n g j v)
    (HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i))
    hS (by simpa [hwidth] using hgap j) hdelta
  rw [hleaf]
  simpa [S] using hstable

private theorem chunkCoords_pairwise_disjoint {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n))
    (j k : Fin (HypercubeRamsey.S04.chunkNum β γ n)) (hjk : j ≠ k) :
    Disjoint (HypercubeRamsey.S04.chunkCoords β γ n g j)
      (HypercubeRamsey.S04.chunkCoords β γ n g k) := by
  classical
  let s := HypercubeRamsey.S04.chunkNum β γ n
  let ℓ := HypercubeRamsey.S04.chunkLen β γ n
  have hs : 0 < s := by omega
  have hstart :
      HypercubeRamsey.S04.chunkStart β γ n g j + ℓ ≤
          HypercubeRamsey.S04.chunkStart β γ n g k ∨
        HypercubeRamsey.S04.chunkStart β γ n g k + ℓ ≤
          HypercubeRamsey.S04.chunkStart β γ n g j := by
    by_cases hjk' : j.val < k.val
    · have hidx : g.val * s + j.val + 1 ≤ g.val * s + k.val := by omega
      have hmul := Nat.mul_le_mul_right ℓ hidx
      left
      calc
        HypercubeRamsey.S04.chunkStart β γ n g j + ℓ =
            (g.val * s + j.val + 1) * ℓ := by
              simp [HypercubeRamsey.S04.chunkStart, s, ℓ, Nat.add_mul,
                Nat.mul_add, Nat.add_assoc]
        _ ≤ (g.val * s + k.val) * ℓ := hmul
        _ = HypercubeRamsey.S04.chunkStart β γ n g k := by
              simp [HypercubeRamsey.S04.chunkStart, s, ℓ]
    · have hkj' : k.val < j.val := by
        have hne : j.val ≠ k.val := by intro h; exact hjk (Fin.ext h)
        omega
      have hidx : g.val * s + k.val + 1 ≤ g.val * s + j.val := by omega
      have hmul := Nat.mul_le_mul_right ℓ hidx
      right
      calc
        HypercubeRamsey.S04.chunkStart β γ n g k + ℓ =
            (g.val * s + k.val + 1) * ℓ := by
              simp [HypercubeRamsey.S04.chunkStart, s, ℓ, Nat.add_mul,
                Nat.mul_add, Nat.add_assoc]
        _ ≤ (g.val * s + j.val) * ℓ := hmul
        _ = HypercubeRamsey.S04.chunkStart β γ n g j := by
              simp [HypercubeRamsey.S04.chunkStart, s, ℓ]
  apply Finset.disjoint_left.mpr
  intro i hi hj'
  rcases Finset.mem_filter.mp hi with ⟨_, ⟨hlo₁, hhi₁⟩⟩
  rcases Finset.mem_filter.mp hj' with ⟨_, ⟨hlo₂, hhi₂⟩⟩
  rcases hstart with h | h
  · have hle₁ : i.val < HypercubeRamsey.S04.chunkStart β γ n g j + ℓ := by
      simpa [HypercubeRamsey.S04.chunkLen, ℓ] using hhi₁
    have hle₂ : HypercubeRamsey.S04.chunkStart β γ n g k ≤ i.val := by
      exact hlo₂
    omega
  · have hle₁ : i.val < HypercubeRamsey.S04.chunkStart β γ n g k + ℓ := by
      simpa [HypercubeRamsey.S04.chunkLen, ℓ] using hhi₂
    have hle₂ : HypercubeRamsey.S04.chunkStart β γ n g j ≤ i.val := by
      exact hlo₁
    omega

private theorem clipped_tuple_flip_profile {β γ : ℝ} {n : ℕ}
    (g : Fin (HypercubeRamsey.S04.gadgetNum β γ n)) (v : CubeVertex n) (i : Fin n) :
    (∀ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) =
        HypercubeRamsey.S04.clipped β γ n g j v) ∨
    ∃ j : Fin (HypercubeRamsey.S04.chunkNum β γ n),
      (∀ k, k ≠ j →
        HypercubeRamsey.S04.clipped β γ n g k (HypercubeRamsey.cubeFlip v i) =
          HypercubeRamsey.S04.clipped β γ n g k v) ∧
      (HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) =
          HypercubeRamsey.S04.clipped β γ n g j v + 1 ∨
        HypercubeRamsey.S04.clipped β γ n g j v =
          HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) + 1) := by
  classical
  let D : Finset (Fin (HypercubeRamsey.S04.chunkNum β γ n)) :=
    Finset.univ.filter fun j =>
      HypercubeRamsey.S04.clipped β γ n g j (HypercubeRamsey.cubeFlip v i) ≠
        HypercubeRamsey.S04.clipped β γ n g j v
  have hcard : D.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    by_contra hjk
    have hij : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g j := by
      by_contra hnot
      have hcount := chunkCount_flip_eq g j v i hnot
      have hclip : HypercubeRamsey.S04.clipped β γ n g j
          (HypercubeRamsey.cubeFlip v i) = HypercubeRamsey.S04.clipped β γ n g j v := by
        simp [HypercubeRamsey.S04.clipped, hcount]
      exact (Finset.mem_filter.mp hj).2 hclip
    have hik : i ∈ HypercubeRamsey.S04.chunkCoords β γ n g k := by
      by_contra hnot
      have hcount := chunkCount_flip_eq g k v i hnot
      have hclip : HypercubeRamsey.S04.clipped β γ n g k
          (HypercubeRamsey.cubeFlip v i) = HypercubeRamsey.S04.clipped β γ n g k v := by
        simp [HypercubeRamsey.S04.clipped, hcount]
      exact (Finset.mem_filter.mp hk).2 hclip
    exact (Finset.disjoint_left.mp (chunkCoords_pairwise_disjoint g j k hjk) hij) hik
  by_cases hempty : D = ∅
  · left
    intro j
    by_contra hne
    have hj : j ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hempty] at hj
    simp at hj
  · have hDne : D.card ≠ 0 := by
      intro h
      exact hempty (Finset.card_eq_zero.mp h)
    have hDcard : D.card = 1 := by omega
    obtain ⟨j, hjD⟩ := Finset.card_eq_one.mp hDcard
    right
    refine ⟨j, ?_, ?_⟩
    · intro k hkj
      by_contra hne
      have hk : k ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
      rw [hjD] at hk
      simp [hkj] at hk
    · have hjmem : j ∈ D := by rw [hjD]; simp
      have hjdiff := (Finset.mem_filter.mp hjmem).2
      have hdelta := clipped_flip_delta g j v i (by
        by_contra hnot
        have hcount := chunkCount_flip_eq g j v i hnot
        have hclip : HypercubeRamsey.S04.clipped β γ n g j
            (HypercubeRamsey.cubeFlip v i) = HypercubeRamsey.S04.clipped β γ n g j v := by
          simp [HypercubeRamsey.S04.clipped, hcount]
        exact hjdiff hclip)
      by_cases hle : HypercubeRamsey.S04.clipped β γ n g j
          (HypercubeRamsey.cubeFlip v i) ≤ HypercubeRamsey.S04.clipped β γ n g j v
      · right
        omega
      · left
        omega

private theorem exists_cubeFlip_of_adj {n : ℕ} (u v : CubeVertex n)
    (h : (cube n).Adj u v) : ∃ i : Fin n, HypercubeRamsey.cubeFlip u i = v := by
  classical
  have hdiff :
      (Finset.univ.filter fun i : Fin n => u i ≠ v i).card = 1 := h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hdiff
  have hAtI : u i ≠ v i := by
    have hmem : i ∈ Finset.univ.filter fun k : Fin n => u k ≠ v k := by
      rw [hi]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨i, ?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    cases hu : u i <;> cases hv : v i <;> simp_all [HypercubeRamsey.cubeFlip]
  · have hnot : k ∉ Finset.univ.filter fun k' : Fin n => u k' ≠ v k' := by
      rw [hi]
      simpa using hki
    have hsame : u k = v k := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp [HypercubeRamsey.cubeFlip, hki, hsame]

private theorem oddAdj_subset_coordinate_flips {β γ : ℝ} {n : ℕ}
    (u : OddRole n) :
    HypercubeRamsey.S04.oddAdj u ⊆
      Finset.univ.image (fun i : Fin n => HypercubeRamsey.cubeFlip u.1 i) := by
  intro v hv
  have hadj : (cube n).Adj u.1 v := (Finset.mem_filter.mp hv).2
  rcases exists_cubeFlip_of_adj u.1 v hadj with ⟨i, rfl⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem keyFlip_image_card_le_n {β γ : ℝ} {n : ℕ} (u : OddRole n) :
    (HypercubeRamsey.S04.Zset β γ u).card ≤ n := by
  classical
  let F : Finset (HypercubeRamsey.S04.Key β γ n) :=
    Finset.univ.image fun i : Fin n =>
      HypercubeRamsey.S04.key β γ n (HypercubeRamsey.cubeFlip u.1 i)
  have hsub : HypercubeRamsey.S04.Zset β γ u ⊆ F := by
    intro κ hκ
    rcases Finset.mem_image.mp hκ with ⟨v, hv, rfl⟩
    rcases exists_cubeFlip_of_adj u.1 v ((Finset.mem_filter.mp hv).2) with ⟨i, hi⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hi]⟩
  calc
    (HypercubeRamsey.S04.Zset β γ u).card ≤ F.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp [F]

end HypercubeRamsey.Lane_q_s04_gadget
