import HypercubeRamsey.S15.Masks
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace HypercubeRamsey.Lane_q_s15_c2

open Classical HypercubeRamsey.S15 OAI.HypercubeRamsey
open Filter
open scoped BigOperators

private theorem cluster_heq_of_dependent_apply {α : Sort*} {β : α → Sort*}
    (f : ∀ a, β a) {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

theorem expect_map {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : HypercubeRamsey.FinLaw α) (f : α → β) (F : β → ℝ) :
    (HypercubeRamsey.FinLaw.map P f).E F = P.E (fun a => F (f a)) := by
  classical
  simp only [HypercubeRamsey.FinLaw.E, HypercubeRamsey.FinLaw.map]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b hb hne
    simp [eq_comm, hne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

theorem expect_bind {α β : Type*} [Fintype α] [Fintype β]
    (P : HypercubeRamsey.FinLaw α) (K : α → HypercubeRamsey.FinLaw β)
    (F : α × β → ℝ) :
    (HypercubeRamsey.FinLaw.bind P K).E F =
      P.E (fun a => (K a).E (fun b => F (a, b))) := by
  classical
  simp only [HypercubeRamsey.FinLaw.E, HypercubeRamsey.FinLaw.bind]
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem expect_of_map_eq_bind {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq (β × γ)]
    (P : HypercubeRamsey.FinLaw α) (f : α → β × γ)
    (Q : HypercubeRamsey.FinLaw β) (K : β → HypercubeRamsey.FinLaw γ)
    (h : HypercubeRamsey.FinLaw.map P f = HypercubeRamsey.FinLaw.bind Q K)
    (F : β × γ → ℝ) :
    P.E (fun a => F (f a)) = Q.E (fun b => (K b).E (fun c => F (b, c))) := by
  calc
    P.E (fun a => F (f a)) = (HypercubeRamsey.FinLaw.map P f).E F :=
      (expect_map P f F).symm
    _ = (HypercubeRamsey.FinLaw.bind Q K).E F := by rw [h]
    _ = Q.E (fun b => (K b).E (fun c => F (b, c))) := expect_bind Q K F

private def cubeWordRank {n : ℕ} (v : CubePos n) : ℕ :=
  ∑ j : Fin n, if v j then 2 ^ j.val else 0

private theorem cubeWordRank_eq_ofDigits {n : ℕ} (v : CubePos n) :
    cubeWordRank v = Nat.ofDigits 2 (List.ofFn fun j : Fin n => if v j then 1 else 0) := by
  classical
  simp [cubeWordRank, Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn]

private theorem cubeWordRank_injective {n : ℕ} : Function.Injective (cubeWordRank (n := n)) := by
  intro v w h
  have hv := cubeWordRank_eq_ofDigits v
  have hw := cubeWordRank_eq_ofDigits w
  have hdigits : Nat.ofDigits 2 (List.ofFn fun j : Fin n => if v j then 1 else 0) =
      Nat.ofDigits 2 (List.ofFn fun j : Fin n => if w j then 1 else 0) := by
    calc
      _ = cubeWordRank v := hv.symm
      _ = cubeWordRank w := h
      _ = _ := hw
  have hlist := Nat.ofDigits_inj_of_len_eq (b := 2) (by norm_num)
    (by simp)
    (by
      simp only [List.forall_mem_ofFn_iff]
      intro j
      cases v j <;> norm_num)
    (by
      simp only [List.forall_mem_ofFn_iff]
      intro j
      cases w j <;> norm_num)
    hdigits
  have hfun : (fun j : Fin n => if v j then 1 else 0) =
      (fun j : Fin n => if w j then 1 else 0) := List.ofFn_injective hlist
  funext j
  have hval := congrFun hfun j
  cases hvj : v j <;> cases hwj : w j <;> simp_all [hvj, hwj]

private theorem cubeWordRank_lt_pow {n : ℕ} (v : CubePos n) : cubeWordRank v < 2 ^ n := by
  rw [cubeWordRank_eq_ofDigits]
  have hdigits : ∀ d ∈ List.ofFn (fun j : Fin n => if v j then 1 else 0), d < 2 := by
    simp only [List.forall_mem_ofFn_iff]
    intro j
    cases v j <;> norm_num
  calc
    Nat.ofDigits 2 (List.ofFn fun j : Fin n => if v j then 1 else 0) <
        2 ^ (List.ofFn (fun j : Fin n => if v j then 1 else 0)).length :=
      Nat.ofDigits_lt_base_pow_length (by norm_num) hdigits
    _ = 2 ^ n := by simp

theorem clusterQueryOrder_injective {T : Stage} {k : ℕ} :
    Function.Injective (clusterQueryOrder (T := T) (k := k)) := by
  classical
  intro q q' horder
  have hcode : q.1.val * 2 ^ (T.S.n k) + cubeWordRank q.2.1 =
      q'.1.val * 2 ^ (T.S.n k) + cubeWordRank q'.2.1 := by
    simpa [clusterQueryOrder, cubeWordRank] using horder
  have hnpos : 0 < 2 ^ (T.S.n k) := Nat.pow_pos (by decide)
  have hc1 := cubeWordRank_lt_pow q.2.1
  have hc2 := cubeWordRank_lt_pow q'.2.1
  have hrem : cubeWordRank q.2.1 = cubeWordRank q'.2.1 := by
    have h := congrArg (fun z : ℕ => z % 2 ^ (T.S.n k)) hcode
    simpa [Nat.mul_add_mod_of_lt hc1, Nat.mul_add_mod_of_lt hc2] using h
  have hdiv : q.1.val = q'.1.val := by
    have h := congrArg (fun z : ℕ => z / 2 ^ (T.S.n k)) hcode
    rw [Nat.mul_comm q.1.val, Nat.mul_comm q'.1.val,
      Nat.mul_add_div hnpos, Nat.div_eq_of_lt hc1,
      Nat.mul_add_div hnpos, Nat.div_eq_of_lt hc2] at h
    exact Nat.add_right_cancel h
  apply Prod.ext
  · exact Fin.ext hdiv
  · apply Subtype.ext
    exact cubeWordRank_injective hrem

private theorem position_eq_of_internal_outside {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    {v w : Position T k}
    (hint : internalWord PT hPT i v = internalWord PT hPT i w)
    (hout : outsideWord PT hPT i v = outsideWord PT hPT i w) : v = w := by
  funext t
  by_cases ht : t.val < T.S.n k - (PT.tiling.P i).h
  · have h := congrFun hout ⟨t.val, ht⟩
    simpa [outsideWord] using h
  · let j : Fin (PT.tiling.P i).h :=
      ⟨t.val - (T.S.n k - (PT.tiling.P i).h), by
        have hnh := Nat.sub_le (T.S.n k) (PT.tiling.P i).h
        have hj := clusterHeight_le PT hPT i
        omega⟩
    have hidx : (⟨T.S.n k - (PT.tiling.P i).h + j.val,
        by
          have hh := clusterHeight_le PT hPT i
          have hj := j.isLt
          omega⟩ : Fin (T.S.n k)) = t := by
      apply Fin.ext
      dsimp [j]
      omega
    have h := congrFun hint j
    simpa [internalWord, hidx] using h

private theorem position_eq_of_internal_outside_heq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) {i j : Fin PT.tiling.m}
    {v w : Position T k}
    (hij : i = j)
    (hint : HEq (internalWord PT hPT i v) (internalWord PT hPT j w))
    (hout : HEq (outsideWord PT hPT i v) (outsideWord PT hPT j w)) : v = w := by
  cases hij
  exact position_eq_of_internal_outside PT hPT i (eq_of_heq hint) (eq_of_heq hout)

theorem position_eq_of_same_slice_and_internal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    {v w : Position T k}
    (hs : clusterSliceAt PT hPT v = clusterSliceAt PT hPT w)
    (hint : HEq (clusterWordAt PT hPT v) (clusterWordAt PT hPT w)) : v = w := by
  have hi : patchAt PT hPT v = patchAt PT hPT w := congrArg Sigma.fst hs
  have hout : HEq (outsideWord PT hPT (patchAt PT hPT v) v)
      (outsideWord PT hPT (patchAt PT hPT w) w) :=
    cluster_heq_of_dependent_apply (fun s : ClusterSlice PT => s.2.1) hs
  have hint' : HEq (internalWord PT hPT (patchAt PT hPT v) v)
      (internalWord PT hPT (patchAt PT hPT w) w) := by
    simpa [clusterWordAt] using hint
  exact position_eq_of_internal_outside_heq PT hPT hi hint' hout

private noncomputable def clusterSliceWord {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (b : OddPosition T k) : Σ s : ClusterSlice PT, IWord PT.tiling s.1 :=
  ⟨clusterSliceAt PT hPT b.1, clusterWordAt PT hPT b.1⟩

theorem clusterSliceWord_injective {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) :
    Function.Injective (clusterSliceWord (hPT := hPT)) := by
  intro b b' h
  have hparts := Sigma.mk.inj_iff.mp h
  have hpos := position_eq_of_same_slice_and_internal hPT hparts.1 hparts.2
  exact Subtype.ext hpos

private theorem solverWordAt_odd {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (b : OddPosition T k) :
    ¬ HypercubeRamsey.IsEvenRole (solverWordAt PT hPT hm b.1) := by
  classical
  unfold solverWordAt
  dsimp
  split_ifs with h
  · intro hz
    exact b.2 (h.mp hz)
  · have hz : HypercubeRamsey.IsEvenRole (clusterWordAt PT hPT b.1) := by
      by_contra hnot
      apply h
      constructor
      · exact fun hz => (hnot hz).elim
      · exact fun hb => (b.2 hb).elim
    intro hflip
    exact ((evenRole_flipPos _ _).mp hflip) hz

private theorem flipPos_involutive {n : ℕ} (v : CubePos n) (j : Fin n) :
    flipPos (flipPos v j) j = v := by
  funext t
  by_cases ht : t = j <;> simp [flipPos, ht]

private theorem clusterGroupFiber_card {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {g : ClusterGroupIndex PT} :
    (groupFiber g.2).card = (PT.tiling.P g.1.1).h := by
  classical
  unfold groupFiber
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro l hl l' hl' heq
    by_contra hne
    have hval := congrFun heq l
    cases hz : g.2.1 l <;> simp [flipPos, hne, hz] at hval

private noncomputable def clusterGroupWordChoices {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (g : ClusterGroupIndex PT) :
    Finset (Σ s : ClusterSlice PT, IWord PT.tiling s.1) := by
  classical
  let e0 : Fin (PT.tiling.P g.1.1).h :=
    ⟨0, clusterHeight_pos PT hPT hm g.1.1⟩
  exact (groupFiber g.2).image (fun z => (⟨g.1, z⟩ :
      Σ s : ClusterSlice PT, IWord PT.tiling s.1)) ∪
    (groupFiber g.2).image (fun z => (⟨g.1, flipPos z e0⟩ :
      Σ s : ClusterSlice PT, IWord PT.tiling s.1))

private theorem clusterGroupWordChoices_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (g : ClusterGroupIndex PT) :
    (clusterGroupWordChoices hPT hm g).card ≤ 2 * (PT.tiling.P g.1.1).h := by
  classical
  unfold clusterGroupWordChoices
  dsimp
  calc
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (groupFiber g.2).card + (groupFiber g.2).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * (PT.tiling.P g.1.1).h := by rw [clusterGroupFiber_card]; omega

private theorem clusterSliceWord_mem_groupChoices {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (b : OddPosition T k) :
    clusterSliceWord hPT b ∈ clusterGroupWordChoices hPT hm
      (clusterGroupIndexAt PT hPT hm b) := by
  classical
  let i := patchAt PT hPT b.1
  let z := clusterWordAt PT hPT b.1
  let e0 : Fin (PT.tiling.P i).h := ⟨0, clusterHeight_pos PT hPT hm i⟩
  have hmem : solverWordAt PT hPT hm b.1 ∈
      groupFiber ((clusterGroupIndexAt PT hPT hm b).2) := by
    change solverWordAt PT hPT hm b.1 ∈
      groupFiber ((clusterSolver PT hPT hm (clusterSliceAt PT hPT b.1).1).groupOf
        (solverWordAt PT hPT hm b.1))
    exact (clusterSolver PT hPT hm (clusterSliceAt PT hPT b.1).1).groupOf_spec _
      (solverWordAt_odd hPT hm b)
  by_cases hpar : HypercubeRamsey.IsEvenRole z ↔ HypercubeRamsey.IsEvenRole b.1
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨solverWordAt PT hPT hm b.1, ?_, ?_⟩
    · simpa [clusterGroupWordChoices, clusterGroupIndexAt, clusterSliceAt] using hmem
    · dsimp [clusterGroupIndexAt, clusterSliceWord]
      have hpar' : HypercubeRamsey.IsEvenRole (clusterWordAt PT hPT b.1) ↔
          HypercubeRamsey.IsEvenRole b.1 := by simpa [z] using hpar
      have hword : clusterWordAt PT hPT b.1 = solverWordAt PT hPT hm b.1 := by
        simp [solverWordAt, hpar']
      exact (Sigma.mk.inj_iff).2 ⟨rfl, heq_of_eq hword.symm⟩
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨solverWordAt PT hPT hm b.1, ?_, ?_⟩
    · simpa [clusterGroupWordChoices, clusterGroupIndexAt, clusterSliceAt] using hmem
    · dsimp [clusterGroupIndexAt, clusterSliceWord]
      have hpar' : ¬ (HypercubeRamsey.IsEvenRole (clusterWordAt PT hPT b.1) ↔
          HypercubeRamsey.IsEvenRole b.1) := by simpa [z] using hpar
      have hword : clusterWordAt PT hPT b.1 =
          flipPos (solverWordAt PT hPT hm b.1) e0 := by
        simp [solverWordAt, hpar']
        exact (flipPos_involutive (clusterWordAt PT hPT b.1) e0).symm
      exact (Sigma.mk.inj_iff).2 ⟨rfl, heq_of_eq hword.symm⟩

noncomputable def clusterKeptStarScope {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (M : ClusterMask PT) : Finset (OddPosition T k) :=
  (Finset.univ.filter fun p : Fin (T.S.n k) × Fin (T.S.n k) =>
    p.1 ∈ clusterKeptRows M).image (fun p =>
      ⟨flipPos (M.positions p.1).1 p.2,
        by
          intro hEven
          exact (evenRole_flipPos (M.positions p.1).1 p.2).mp hEven (M.positions p.1).2⟩)

theorem clusterKeptStarScope_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (M : ClusterMask PT) :
    (clusterKeptStarScope M).card ≤ (T.S.n k) ^ 2 := by
  classical
  unfold clusterKeptStarScope
  calc
    _ ≤ (Finset.univ.filter fun p : Fin (T.S.n k) × Fin (T.S.n k) =>
        p.1 ∈ clusterKeptRows M).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin (T.S.n k) × Fin (T.S.n k))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (T.S.n k) ^ 2 := by simp [Nat.pow_two]

theorem clusterKeptStarScope_card_real_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (M : ClusterMask PT) :
    ((clusterKeptStarScope M).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
  exact_mod_cast clusterKeptStarScope_card_le M

theorem clusterKeptStarScope_contains_adjacent {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {M : ClusterMask PT} {r : Fin (T.S.n k)}
    (hr : r ∈ clusterKeptRows M) {b : OddPosition T k}
    (hAdj : Adjacent (M.positions r) b) : b ∈ clusterKeptStarScope M := by
  classical
  have hdiff : (Finset.univ.filter fun t : Fin (T.S.n k) =>
      (M.positions r).1 t ≠ b.1 t).card = 1 := hAdj
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hdiff
  have hjmem : j ∈ Finset.univ.filter fun t : Fin (T.S.n k) =>
      (M.positions r).1 t ≠ b.1 t := by
    rw [hj]
    simp
  have hdiffj : (M.positions r).1 j ≠ b.1 j :=
    (Finset.mem_filter.mp hjmem).2
  have hsame : ∀ t, t ≠ j → (M.positions r).1 t = b.1 t := by
    intro t ht
    have hnot : t ∉ Finset.univ.filter fun t : Fin (T.S.n k) =>
        (M.positions r).1 t ≠ b.1 t := by
      rw [hj]
      simp [ht]
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  have hcoord : b.1 = flipPos (M.positions r).1 j := by
    funext t
    by_cases ht : t = j
    · subst t
      cases ha : (M.positions r).1 j <;> cases hb : b.1 j <;>
        simp_all [flipPos]
    · have h := hsame t ht
      simp [flipPos, ht, h]
  apply Finset.mem_image.mpr
  refine ⟨(r, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, ?_⟩
  apply Subtype.ext
  exact hcoord.symm

noncomputable def clusterKeptProductScope {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (M : ClusterMask PT) :
    Finset (OddPosition T k) :=
  (clusterKeptStarScope M).filter fun b =>
    ∃ r, r ∈ clusterKeptRows M ∧ Adjacent (M.positions r) b ∧
      (b ∈ clusterBulkNeighbours PT hPT (M.positions r) ∨
        (r, b) ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins ∨
          clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT (M.positions r).1)

theorem clusterKeptProductScope_card_real_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (M : ClusterMask PT) :
    ((clusterKeptProductScope hPT M).card : ℝ) ≤ (T.S.n k : ℝ) ^ 2 := by
  have hcard : (clusterKeptProductScope hPT M).card ≤ (T.S.n k) ^ 2 := by
    calc
      (clusterKeptProductScope hPT M).card ≤ (clusterKeptStarScope M).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ (T.S.n k) ^ 2 := clusterKeptStarScope_card_le M
  exact_mod_cast hcard

theorem clusterKeptProductScope_contains_bulk {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) {M : ClusterMask PT}
    {r : Fin (T.S.n k)} (hr : r ∈ clusterKeptRows M) {b : OddPosition T k}
    (hb : b ∈ clusterBulkNeighbours PT hPT (M.positions r)) :
    b ∈ clusterKeptProductScope hPT M := by
  classical
  have hAdj : Adjacent (M.positions r) b := by
    simpa [clusterBulkNeighbours] using (Finset.mem_filter.mp hb).2.1
  have hstar := clusterKeptStarScope_contains_adjacent (M := M) hr hAdj
  exact Finset.mem_filter.mpr ⟨hstar, ⟨r, hr, hAdj, Or.inl hb⟩⟩

theorem clusterKeptProductScope_contains_crossing {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) {M : ClusterMask PT}
    {q : Fin (T.S.n k) × OddPosition T k}
    (hq : q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins) :
    q.2 ∈ clusterKeptProductScope hPT M := by
  classical
  have hallowed : q ∈ clusterAllowedCrossings PT hPT M := (Finset.mem_sdiff.mp hq).1
  have hparts := Finset.mem_filter.mp hallowed
  have hrow : q.1 ∈ clusterKeptRows M := hparts.2.1
  have hroles := Finset.mem_filter.mp hparts.2.2.2
  have hAdj : Adjacent (M.positions q.1) q.2 := hroles.2.1
  have hstar := clusterKeptStarScope_contains_adjacent (M := M) hrow hAdj
  exact Finset.mem_filter.mpr ⟨hstar, ⟨q.1, hrow, hAdj, Or.inr (Or.inl hq)⟩⟩

private theorem clusterMaskConsistent_small_parts {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (M : ClusterMask PT) (B : ClusterBinAssignment PT)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B) :
    (∀ r, r ∈ M.coreBins ↔ r ∉ M.geometric ∧ clusterCoreRepeat PT hPT hm M B r) ∧
    (∀ q, q ∈ M.crossingBins ↔ q ∈ clusterAllowedCrossings PT hPT M ∧
      clusterCrossingRepeat PT hPT hm M B q) := by
  classical
  unfold ClusterMaskConsistent at hcons
  rw [if_pos hsmall] at hcons
  exact hcons

theorem clusterConsistent_no_unremoved_crossing_repeat {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (M : ClusterMask PT) (B : ClusterBinAssignment PT)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    {p q : Fin (T.S.n k) × OddPosition T k}
    (hp : p ∈ clusterAllowedCrossings PT hPT M)
    (hq : q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins)
    (horder : clusterQueryOrder p < clusterQueryOrder q) :
    (B (clusterGroupIndexAt PT hPT hm p.2)).1 ≠
      (B (clusterGroupIndexAt PT hPT hm q.2)).1 := by
  classical
  intro hbin
  have hAvoided : ¬ clusterCrossingRepeat PT hPT hm M B q := by
    intro hrep
    have hqmem := (clusterMaskConsistent_small_parts M B hsmall hcons).2 q
    have hcross := hqmem.mpr ⟨(Finset.mem_sdiff.mp hq).1,
      ⟨p, hp, horder, hbin⟩⟩
    exact (Finset.mem_sdiff.mp hq).2 hcross
  exact hAvoided ⟨p, hp, horder, hbin⟩

theorem clusterConsistent_no_core_repeat_across_kept {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (M : ClusterMask PT) (B : ClusterBinAssignment PT)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    {r t : Fin (T.S.n k)} (hr : r ∈ clusterKeptRows M) (ht : t ∈ clusterKeptRows M)
    (htr : t < r) {g : ClusterGroupIndex PT}
    (hg : g ∈ clusterCoreGroups PT hPT hm (M.positions r))
    {g' : ClusterGroupIndex PT}
    (hg' : g' ∈ clusterCoreGroups PT hPT hm (M.positions t)) :
    (B g).1 ≠ (B g').1 := by
  classical
  intro hbin
  have hnotGeom : t ∉ M.geometric := by
    have h := (Finset.mem_sdiff.mp ht).2
    exact fun htgeom => h (Finset.mem_union_left _ htgeom)
  have hnotGeomR : r ∉ M.geometric := by
    have h := (Finset.mem_sdiff.mp hr).2
    exact fun hrgeom => h (Finset.mem_union_left _ hrgeom)
  have hrepeat : clusterCoreRepeat PT hPT hm M B r :=
    ⟨t, htr, hnotGeom, g, hg, g', hg', hbin⟩
  have hcore :=
    (clusterMaskConsistent_small_parts M B hsmall hcons).1 r |>.mpr ⟨hnotGeomR, hrepeat⟩
  have hnotCore : r ∉ M.coreBins := by
    have h := (Finset.mem_sdiff.mp hr).2
    exact fun hcore' => h (Finset.mem_union_right _ hcore')
  exact hnotCore hcore

theorem clusterBinGood_separates_star_groups {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    {a : EvenPosition T k} {b b' : OddPosition T k}
    (hsmall : PT.tiling.mode = .highSmall)
    (hAdj : Adjacent a b) (hAdj' : Adjacent a b')
    (hgroups : clusterGroupIndexAt PT hPT hm b ≠ clusterGroupIndexAt PT hPT hm b') :
    (B (clusterGroupIndexAt PT hPT hm b)).1 ≠
    (B (clusterGroupIndexAt PT hPT hm b')).1 :=
  hgood.2.2 hsmall a b b' hAdj hAdj' hgroups

theorem clusterBinGood_same_bin_implies_same_group {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    {a : EvenPosition T k} {b b' : OddPosition T k}
    (hsmall : PT.tiling.mode = .highSmall)
    (hAdj : Adjacent a b) (hAdj' : Adjacent a b')
    (hbin : (B (clusterGroupIndexAt PT hPT hm b)).1 =
      (B (clusterGroupIndexAt PT hPT hm b')).1) :
    clusterGroupIndexAt PT hPT hm b = clusterGroupIndexAt PT hPT hm b' := by
  by_contra hgroups
  exact (clusterBinGood_separates_star_groups W B hgood hsmall hAdj hAdj' hgroups) hbin

theorem clusterBin_sets_disjoint_of_patches {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid)
    {i j : Fin PT.tiling.m} (hij : i ≠ j)
    (D : Bin PT.tiling i) (D' : Bin PT.tiling j) : Disjoint D.1 D'.1 := by
  classical
  have hiSub : D.1 ⊆ (PT.tiling.P i).Y := by
    calc
      D.1 ≤ (PT.tiling.P i).bins.parts.sup id := Finset.le_sup (f := id) D.2
      _ = (PT.tiling.P i).Y := (PT.tiling.P i).bins.sup_parts
  have hjSub : D'.1 ⊆ (PT.tiling.P j).Y := by
    calc
      D'.1 ≤ (PT.tiling.P j).bins.parts.sup id := Finset.le_sup (f := id) D'.2
      _ = (PT.tiling.P j).Y := (PT.tiling.P j).bins.sup_parts
  have hdis := hPT.tiling_valid.patch_Y_disjoint i j hij
  apply Finset.disjoint_left.mpr
  intro y hy hy'
  exact (Finset.disjoint_left.mp hdis) (hiSub hy) (hjSub hy')

private theorem clusterBin_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (i : Fin PT.tiling.m) (D : Bin PT.tiling i) :
    D.1.Nonempty := by
  classical
  by_contra hne
  have hEmpty : D.1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  have hbot : (⊥ : Finset (Fin (T.S.N k))) ∈ (PT.tiling.P i).bins.parts := by
    simpa [hEmpty] using D.2
  exact (PT.tiling.P i).bins.bot_notMem hbot

theorem patchAt_eq_of_evenPatchPosition {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) {i : Fin PT.tiling.m}
    {a : EvenPosition T k} (ha : a ∈ evenPatchPositions PT.tiling i) :
    patchAt PT hPT a.1 = i := by
  classical
  have hleaf : a.1 ∈ PT.tiling.leaf i := (Finset.mem_filter.mp ha).2
  have huniq := (Classical.choose_spec (hPT.tiling_valid.prefix_complete a.1)).2 i hleaf
  change Classical.choose (hPT.tiling_valid.prefix_complete a.1) = i
  exact huniq.symm

theorem clusterCore_crossing_bins_neq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {M : ClusterMask PT} {i : Fin PT.tiling.m}
    (hGeom : ClusterMaskGeometry PT hPT i M)
    {r : Fin (T.S.n k)} (hr : r ∈ clusterKeptRows M)
    {g : ClusterGroupIndex PT} (hg : g ∈ clusterCoreGroups PT hPT hm (M.positions r))
    {q : Fin (T.S.n k) × OddPosition T k}
    (hq : q ∈ clusterAllowedCrossings PT hPT M)
    (D : Bin PT.tiling (g.1.1)) (D' : Bin PT.tiling ((clusterGroupIndexAt PT hPT hm q.2).1.1)) :
    D.1 ≠ D'.1 := by
  classical
  unfold clusterCoreGroups at hg
  obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp hg
  have hcoreParts := Finset.mem_filter.mp hb
  have hcorePatch : patchAt PT hPT b.1 = patchAt PT hPT (M.positions r).1 :=
    hcoreParts.2.2
  have hgPatch : g.1.1 = patchAt PT hPT (M.positions r).1 := by
    calc
      g.1.1 = (clusterGroupIndexAt PT hPT hm b).1.1 := by rw [hbg]
      _ = patchAt PT hPT b.1 := rfl
      _ = patchAt PT hPT (M.positions r).1 := hcorePatch
  have hrow_i : patchAt PT hPT (M.positions r).1 = i :=
    patchAt_eq_of_evenPatchPosition hPT (hGeom.1 r)
  have hqParts := Finset.mem_filter.mp hq
  have hqRow_i : patchAt PT hPT (M.positions q.1).1 = i :=
    patchAt_eq_of_evenPatchPosition hPT (hGeom.1 q.1)
  have hcrossParts := Finset.mem_filter.mp hqParts.2.2.2
  have hcrossPatch : patchAt PT hPT q.2.1 ≠ patchAt PT hPT (M.positions q.1).1 :=
    hcrossParts.2.2
  have hpatchNe : g.1.1 ≠ (clusterGroupIndexAt PT hPT hm q.2).1.1 := by
    have hleft : g.1.1 = i := hgPatch.trans hrow_i
    have hright : (clusterGroupIndexAt PT hPT hm q.2).1.1 = patchAt PT hPT q.2.1 := rfl
    rw [hleft, hright]
    exact fun hEq => hcrossPatch (hEq.symm.trans hqRow_i.symm)
  have hdis := clusterBin_sets_disjoint_of_patches hPT hpatchNe D D'
  intro hEq
  have hNonempty := clusterBin_nonempty PT g.1.1 D
  obtain ⟨y, hy⟩ := hNonempty
  have hy' : y ∈ D'.1 := by simpa [hEq] using hy
  exact (Finset.disjoint_left.mp hdis) hy hy'

theorem flipPos_commute {n : ℕ} (z : CubePos n) (j l : Fin n) :
    flipPos (flipPos z j) l = flipPos (flipPos z l) j := by
  funext t
  by_cases htj : t = j
  · subst t
    by_cases hlj : l = j
    · subst l
      simp [flipPos]
    · simp [flipPos, Ne.symm hlj]
  · by_cases htl : t = l
    · subst t
      simp [flipPos, htj]
    · simp [flipPos, htj, htl, Ne.symm htj, Ne.symm htl]

theorem internalWord_flip_top {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (i : Fin PT.tiling.m)
    (a : Position T k) (l : Fin (PT.tiling.P i).h) :
    internalWord PT hPT i
        (flipPos a ⟨T.S.n k - (PT.tiling.P i).h + l.val,
          by have hh := clusterHeight_le PT hPT i; have hl := l.isLt; omega⟩) =
      flipPos (internalWord PT hPT i a) l := by
  classical
  let j : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P i).h + l.val,
    by have hh := clusterHeight_le PT hPT i; have hl := l.isLt; omega⟩
  have hj : j.val = T.S.n k - (PT.tiling.P i).h + l.val := rfl
  funext t
  by_cases ht : t = l
  · subst t
    simp [internalWord, flipPos, j]
  · have hcoord :
        (⟨T.S.n k - (PT.tiling.P i).h + t.val,
          by have hh := clusterHeight_le PT hPT i; have ht' := t.isLt; omega⟩ : Fin (T.S.n k)) ≠ j := by
      intro heq
      apply ht
      apply Fin.ext
      have hv := congrArg Fin.val heq
      rw [hj] at hv
      have hv' : T.S.n k - (PT.tiling.P i).h + t.val =
          T.S.n k - (PT.tiling.P i).h + l.val := by simpa using hv
      exact Nat.add_left_cancel hv'
    simp [internalWord, flipPos, j, ht, hcoord, Ne.symm hcoord]

private theorem heq_of_dependent_apply {α : Sort*} {β : α → Sort*}
    (f : ∀ a, β a) {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

universe u

private theorem subtype_heq_of_cast_data {α β : Type u} {p : α → Prop} {q : β → Prop}
    {x : Subtype p} {y : Subtype q} (hα : α = β) (hpq : HEq p q)
    (hval : HEq x.1 y.1) : HEq x y :=
  (Subtype.heq_iff_coe_heq hα hpq).2 hval

private noncomputable def solverWordOnPatch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (i : Fin PT.tiling.m) (v : Position T k) : IWord PT.tiling i := by
  classical
  let z := internalWord PT hPT i v
  exact if HypercubeRamsey.IsEvenRole z ↔ HypercubeRamsey.IsEvenRole v then z
    else flipPos z ⟨0, clusterHeight_pos PT hPT hm i⟩

private theorem solverWordAt_eq_solverWordOnPatch {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (v : Position T k) :
    solverWordAt PT hPT hm v =
      solverWordOnPatch PT hPT hm (patchAt PT hPT v) v := rfl

theorem patchAt_flip_internal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : Position T k)
    (l : Fin (PT.tiling.P (patchAt PT hPT a)).h) :
    patchAt PT hPT (flipPos a ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a)).h + l.val,
      by have hh := clusterHeight_le PT hPT (patchAt PT hPT a); have hl := l.isLt; omega⟩) =
      patchAt PT hPT a := by
  classical
  let i := patchAt PT hPT a
  have hl : l.val < (PT.tiling.P i).h := by simpa [i] using l.isLt
  let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P i).h + l.val,
    by have hh := clusterHeight_le PT hPT i; omega⟩
  have hmem : a ∈ PT.tiling.leaf i := by
    simpa [i, patchAt] using
      (Classical.choose_spec (hPT.tiling_valid.prefix_complete a)).1
  have hlen := hPT.tiling_valid.prefix_internal_length
  have hℓ : (PT.tiling.P i).ℓ ≤
      Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).ℓ) (Finset.mem_univ i)
  have hh : (PT.tiling.P i).h ≤
      Finset.univ.sup fun j : Fin PT.tiling.m => (PT.tiling.P j).h :=
    Finset.le_sup (f := fun j : Fin PT.tiling.m => (PT.tiling.P j).h) (Finset.mem_univ i)
  have hℓh : (PT.tiling.P i).ℓ + (PT.tiling.P i).h ≤ T.S.n k := by omega
  have hcge : (PT.tiling.P i).ℓ ≤ c.val := by
    simp [c]
    omega
  have hmem' : flipPos a c ∈ PT.tiling.leaf i := by
    change ∀ j : Fin (T.S.n k), j.val < (PT.tiling.P i).ℓ →
      flipPos a c j = PT.tiling.w i j
    intro j hj
    have hcenter := hmem j hj
    have hjc : j ≠ c := by
      intro heq
      have hv := congrArg Fin.val heq
      have hv' : j.val = c.val := by simpa using hv
      omega
    simpa [flipPos, hjc] using hcenter
  have huniq :=
    (Classical.choose_spec (hPT.tiling_valid.prefix_complete (flipPos a c))).2 i hmem'
  change Classical.choose (hPT.tiling_valid.prefix_complete (flipPos a c)) = i
  exact huniq.symm

theorem solverWordAt_flip_internal_heq {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid)
    (hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge)
    (a : EvenPosition T k) (l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h) :
    HEq
      (solverWordAt PT hPT hm
        (flipPos a.1 ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
          by have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1); have hl := l.isLt; omega⟩))
      (flipPos (solverWordAt PT hPT hm a.1) l) := by
  classical
  let i := patchAt PT hPT a.1
  have hl : l.val < (PT.tiling.P i).h := by simpa [i] using l.isLt
  let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P i).h + l.val,
    by have hh := clusterHeight_le PT hPT i; omega⟩
  let b := flipPos a.1 c
  have hpatch : patchAt PT hPT b = i := by
    simpa [b, i, c] using patchAt_flip_internal PT hPT a.1 l
  have hword : internalWord PT hPT i b = flipPos (internalWord PT hPT i a.1) l :=
    internalWord_flip_top PT hPT i a.1 l
  have hparity : HypercubeRamsey.IsEvenRole (internalWord PT hPT i b) ↔
      ¬ HypercubeRamsey.IsEvenRole (internalWord PT hPT i a.1) := by
    rw [hword]
    exact evenRole_flipPos _ _
  have hfull : HypercubeRamsey.IsEvenRole b ↔ ¬ HypercubeRamsey.IsEvenRole a.1 :=
    evenRole_flipPos a.1 c
  have hrel :
      (HypercubeRamsey.IsEvenRole (internalWord PT hPT i b) ↔
        HypercubeRamsey.IsEvenRole b) ↔
      (HypercubeRamsey.IsEvenRole (internalWord PT hPT i a.1) ↔
        HypercubeRamsey.IsEvenRole a.1) := by
    rw [hparity, hfull]
    tauto
  have hlocal : solverWordOnPatch PT hPT hm i b =
      flipPos (solverWordOnPatch PT hPT hm i a.1) l := by
    by_cases hA : HypercubeRamsey.IsEvenRole (internalWord PT hPT i a.1) ↔
        HypercubeRamsey.IsEvenRole a.1
    · have hB := hrel.mpr hA
      dsimp [solverWordOnPatch]
      rw [if_pos hB, if_pos hA, hword]
    · have hB : ¬ (HypercubeRamsey.IsEvenRole (internalWord PT hPT i b) ↔
          HypercubeRamsey.IsEvenRole b) := by
        intro h
        exact hA (hrel.mp h)
      let e0 : Fin (PT.tiling.P i).h := ⟨0, clusterHeight_pos PT hPT hm i⟩
      calc
        solverWordOnPatch PT hPT hm i b =
        flipPos (flipPos (internalWord PT hPT i a.1) l) e0 := by
          dsimp [solverWordOnPatch]
          rw [if_neg hB, hword]
        _ = flipPos (flipPos (internalWord PT hPT i a.1) e0) l :=
          flipPos_commute _ _ _
        _ = flipPos (solverWordOnPatch PT hPT hm i a.1) l := by
          dsimp [solverWordOnPatch]
          rw [if_neg hA]
  have h0 : HEq (solverWordAt PT hPT hm b)
      (solverWordOnPatch PT hPT hm (patchAt PT hPT b) b) :=
    heq_of_eq (solverWordAt_eq_solverWordOnPatch PT hPT hm b)
  have h1 : HEq (solverWordOnPatch PT hPT hm (patchAt PT hPT b) b)
      (solverWordOnPatch PT hPT hm i b) :=
    heq_of_dependent_apply (fun j => solverWordOnPatch PT hPT hm j b) hpatch
  have h2 : HEq (flipPos (solverWordOnPatch PT hPT hm i a.1) l)
      (flipPos (solverWordAt PT hPT hm a.1) l) :=
    heq_of_eq (congrArg (fun z => flipPos z l)
      (solverWordAt_eq_solverWordOnPatch PT hPT hm a.1).symm)
  exact (h0.trans h1).trans ((heq_of_eq hlocal).trans h2)

theorem clusterSliceAt_flip_internal {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (hPT : PT.Valid) (a : Position T k)
    (l : Fin (PT.tiling.P (patchAt PT hPT a)).h) :
    clusterSliceAt PT hPT
        (flipPos a ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a)).h + l.val,
          by have hh := clusterHeight_le PT hPT (patchAt PT hPT a); have hl := l.isLt; omega⟩) =
      clusterSliceAt PT hPT a := by
  classical
  have hl : l.val < (PT.tiling.P (patchAt PT hPT a)).h := l.isLt
  let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a)).h + l.val,
    by have hh := clusterHeight_le PT hPT (patchAt PT hPT a); omega⟩
  have hpatch : patchAt PT hPT (flipPos a c) = patchAt PT hPT a := by
    simpa [c] using patchAt_flip_internal PT hPT a l
  have hout : outsideWord PT hPT (patchAt PT hPT a) (flipPos a c) =
      outsideWord PT hPT (patchAt PT hPT a) a := by
    funext j
    let jfull : Fin (T.S.n k) := ⟨j.val, by
      have hj := j.isLt
      have hh := clusterHeight_le PT hPT (patchAt PT hPT a)
      omega⟩
    have hbase : T.S.n k - (PT.tiling.P (patchAt PT hPT a)).h ≤ c.val := by
      change T.S.n k - (PT.tiling.P (patchAt PT hPT a)).h ≤
        T.S.n k - (PT.tiling.P (patchAt PT hPT a)).h + l.val
      exact Nat.le_add_right _ _
    have hlt : j.val < c.val := lt_of_lt_of_le j.isLt hbase
    have hjc : jfull ≠ c := by
      intro heq
      have hv := congrArg Fin.val heq
      apply (Nat.ne_of_lt hlt)
      simpa [jfull] using hv
    simp [outsideWord, flipPos, jfull, hjc]
  unfold clusterSliceAt
  refine Sigma.ext hpatch ?_
  apply subtype_heq_of_cast_data
  · exact congrArg (fun i : Fin PT.tiling.m =>
      CubeVertex (T.S.n k - (PT.tiling.P i).h)) hpatch
  · exact heq_of_dependent_apply (fun i : Fin PT.tiling.m =>
      fun o : CubeVertex (T.S.n k - (PT.tiling.P i).h) =>
        ∀ j : Fin (T.S.n k - (PT.tiling.P i).h), j.val < (PT.tiling.P i).ℓ →
          o j = PT.tiling.w i ⟨j.val, by have hj := j.isLt; omega⟩) hpatch
  · exact (heq_of_dependent_apply (fun j : Fin PT.tiling.m =>
      outsideWord PT hPT j (flipPos a c)) hpatch).trans (heq_of_eq hout)

theorem clusterLabelFromInternal_internalNeighbor {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (I : ClusterInternalData PT) (a : EvenPosition T k)
    (l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h) :
    clusterLabelFromInternal (hPT := hPT) hm I
      ⟨flipPos a.1 ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
        by have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1); have hl := l.isLt; omega⟩,
        by
          intro hEven
          exact (evenRole_flipPos a.1 ⟨T.S.n k -
            (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
              by have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1); have hl := l.isLt; omega⟩).mp
              hEven a.2⟩ =
      (I (clusterSliceAt PT hPT a.1)).2
        (flipPos (clusterCenterRole PT hPT hm a).1 l) := by
  classical
  let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
    by have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1); have hl := l.isLt; omega⟩
  let b : OddPosition T k := ⟨flipPos a.1 c, by
    intro hEven
    exact (evenRole_flipPos a.1 c).mp hEven a.2⟩
  have hslice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1 := by
    simpa [b, c] using clusterSliceAt_flip_internal PT hPT a.1 l
  have hword : HEq (solverWordAt PT hPT hm b.1)
      (flipPos (solverWordAt PT hPT hm a.1) l) := by
    simpa [b, c] using solverWordAt_flip_internal_heq PT hPT hm a l
  have harg : (⟨clusterSliceAt PT hPT b.1, solverWordAt PT hPT hm b.1⟩ :
      Σ s : ClusterSlice PT, IWord PT.tiling s.1) =
    ⟨clusterSliceAt PT hPT a.1, flipPos (solverWordAt PT hPT hm a.1) l⟩ :=
      Sigma.ext hslice hword
  unfold clusterLabelFromInternal
  exact congrArg (fun z : Σ s : ClusterSlice PT, IWord PT.tiling s.1 => (I z.1).2 z.2) harg

theorem clusterGroupIndexAt_mem_coreGroups {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (a : EvenPosition T k) (b : OddPosition T k)
    (hAdj : Adjacent a b)
    (hpatch : patchAt PT hPT b.1 = patchAt PT hPT a.1) :
    clusterGroupIndexAt PT hPT hm b ∈ clusterCoreGroups PT hPT hm a := by
  classical
  unfold clusterCoreGroups
  apply Finset.mem_image.mpr
  refine ⟨b, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hAdj, hpatch⟩

theorem coreGroup_bin_eq_for_kept_rows_same_row {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (M : ClusterMask PT) (B : ClusterBinAssignment PT)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    (hstarDistinct : ∀ a b b', Adjacent a b → Adjacent a b' →
      clusterGroupIndexAt PT hPT hm b ≠ clusterGroupIndexAt PT hPT hm b' →
        (B (clusterGroupIndexAt PT hPT hm b)).1 ≠
          (B (clusterGroupIndexAt PT hPT hm b')).1)
    {r t : Fin (T.S.n k)} (hr : r ∈ clusterKeptRows M) (ht : t ∈ clusterKeptRows M)
    {g : ClusterGroupIndex PT} (hg : g ∈ clusterCoreGroups PT hPT hm (M.positions r))
    {g' : ClusterGroupIndex PT} (hg' : g' ∈ clusterCoreGroups PT hPT hm (M.positions t))
    (hbin : (B g).1 = (B g').1) : r = t ∧ g = g' := by
  classical
  by_cases hrt : r = t
  · subst t
    unfold clusterCoreGroups at hg hg'
    obtain ⟨b, hb, hbg⟩ := Finset.mem_image.mp hg
    obtain ⟨b', hb', hbg'⟩ := Finset.mem_image.mp hg'
    have hAdj : Adjacent (M.positions r) b := (Finset.mem_filter.mp hb).2.1
    have hAdj' : Adjacent (M.positions r) b' := (Finset.mem_filter.mp hb').2.1
    have hbgSet : (B (clusterGroupIndexAt PT hPT hm b)).1 = (B g).1 :=
      congrArg (fun g => (B g).1) hbg
    have hbg'Set : (B (clusterGroupIndexAt PT hPT hm b')).1 = (B g').1 :=
      congrArg (fun g => (B g).1) hbg'
    have hgroupsEq : clusterGroupIndexAt PT hPT hm b = clusterGroupIndexAt PT hPT hm b' := by
      by_contra hgroups
      have hsep := hstarDistinct (M.positions r) b b' hAdj hAdj' hgroups
      have hbin' : (B (clusterGroupIndexAt PT hPT hm b)).1 =
          (B (clusterGroupIndexAt PT hPT hm b')).1 := hbgSet.trans (hbin.trans hbg'Set.symm)
      exact hsep hbin'
    have hbin' : (B (clusterGroupIndexAt PT hPT hm b)).1 =
        (B (clusterGroupIndexAt PT hPT hm b')).1 := hbgSet.trans (hbin.trans hbg'Set.symm)
    exact ⟨rfl, hbg.symm.trans (hgroupsEq.trans hbg')⟩
  · rcases lt_or_gt_of_ne hrt with hrt' | htr
    · have hne := clusterConsistent_no_core_repeat_across_kept
        (PT := PT) (hPT := hPT) (hm := hm) M B hsmall hcons ht hr hrt' hg' hg
      exact (hne hbin.symm).elim
    · have hne := clusterConsistent_no_core_repeat_across_kept
        (PT := PT) (hPT := hPT) (hm := hm) M B hsmall hcons hr ht htr hg hg'
      exact (hne hbin).elim

theorem clusterKeptProductScope_core_or_crossing {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {M : ClusterMask PT} {b : OddPosition T k}
    (hb : b ∈ clusterKeptProductScope hPT M) :
    (∃ r, r ∈ clusterKeptRows M ∧ Adjacent (M.positions r) b ∧
      clusterGroupIndexAt PT hPT hm b ∈ clusterCoreGroups PT hPT hm (M.positions r)) ∨
    (∃ r, r ∈ clusterKeptRows M ∧ Adjacent (M.positions r) b ∧
      (r, b) ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins) := by
  classical
  obtain ⟨_, ⟨r, hr, hAdj, hkind⟩⟩ := Finset.mem_filter.mp hb
  rcases hkind with hbulk | hcross | hslice
  · have hbulk' := Finset.mem_filter.mp hbulk
    have hpatch : patchAt PT hPT b.1 = patchAt PT hPT (M.positions r).1 := hbulk'.2.2.1
    exact Or.inl ⟨r, hr, hAdj,
      clusterGroupIndexAt_mem_coreGroups (M.positions r) b hAdj hpatch⟩
  · exact Or.inr ⟨r, hr, hAdj, hcross⟩
  · have hpatch : patchAt PT hPT b.1 = patchAt PT hPT (M.positions r).1 :=
      congrArg Sigma.fst hslice
    exact Or.inl ⟨r, hr, hAdj,
      clusterGroupIndexAt_mem_coreGroups (M.positions r) b hAdj hpatch⟩

theorem clusterKeptProductScope_contains_internal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) {M : ClusterMask PT}
    {r : Fin (T.S.n k)} (hr : r ∈ clusterKeptRows M)
    (l : Fin (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h) :
    (⟨flipPos (M.positions r).1
        ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h + l.val,
          by have hh := clusterHeight_le PT hPT (patchAt PT hPT (M.positions r).1)
             have hl := l.isLt
             omega⟩,
        by
          intro hEven
          exact (evenRole_flipPos (M.positions r).1
            ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h + l.val,
              by have hh := clusterHeight_le PT hPT (patchAt PT hPT (M.positions r).1)
                 have hl := l.isLt
                 omega⟩).mp hEven (M.positions r).2⟩ : OddPosition T k) ∈
      clusterKeptProductScope hPT M := by
  classical
  let a := M.positions r
  have hl : l.val < (PT.tiling.P (patchAt PT hPT a.1)).h := by simpa [a] using l.isLt
  let c : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
    by have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1); omega⟩
  let b : OddPosition T k := ⟨flipPos a.1 c, by
    intro hEven
    exact (evenRole_flipPos a.1 c).mp hEven a.2⟩
  have hslice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1 := by
    simpa [b, c] using clusterSliceAt_flip_internal PT hPT a.1 l
  have hAdj : Adjacent a b := by
      change (Finset.univ.filter fun j : Fin (T.S.n k) => a.1 j ≠ b.1 j).card = 1
      have hfilter : (Finset.univ.filter fun j : Fin (T.S.n k) =>
          a.1 j ≠ flipPos a.1 c j) = {c} := by
        ext j
        by_cases hj : j = c
        · subst j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          simp [flipPos]
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          simp [flipPos, hj]
      rw [hfilter]
      simp
  have hstar := clusterKeptStarScope_contains_adjacent (M := M) hr hAdj
  exact Finset.mem_filter.mpr ⟨hstar, ⟨r, hr, hAdj, Or.inr (Or.inr hslice)⟩⟩

theorem clusterSigma_eq_of_keptStarLabels {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (I I' : ClusterInternalData PT)
    (M : ClusterMask PT) (r : Fin (T.S.n k)) (hr : r ∈ clusterKeptRows M)
    (x : Fin (T.S.N k))
    (hlabels : ∀ b ∈ clusterKeptProductScope hPT M,
      clusterLabelFromInternal (hPT := hPT) hm I b =
        clusterLabelFromInternal (hPT := hPT) hm I' b) :
    clusterSigma PT hPT hm W I (M.positions r) x =
      clusterSigma PT hPT hm W I' (M.positions r) x := by
  classical
  let a := M.positions r
  let s := clusterSliceAt PT hPT a.1
  let S := clusterSolver PT hPT hm s.1
  let v := clusterCenterRole PT hPT hm a
  change S.σ v (historyOnSlice W s) (nbrLabels v.1 (I s).2) x =
    S.σ v (historyOnSlice W s) (nbrLabels v.1 (I' s).2) x
  congr 1
  funext l
  change (I s).2 (flipPos v.1 l) = (I' s).2 (flipPos v.1 l)
  have htype : (PT.tiling.P s.1).h =
      (PT.tiling.P (patchAt PT hPT a.1)).h := rfl
  let l' : Fin (PT.tiling.P (patchAt PT hPT a.1)).h := Fin.cast htype l
  have hl' : l' = l := by
    dsimp [l']
    cases htype
    rfl
  let cₗ : Fin (T.S.n k) := ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
    by have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1); have hl := l.isLt; omega⟩
  let b : OddPosition T k := ⟨flipPos a.1 cₗ, by
    intro hEven
    exact (evenRole_flipPos a.1 cₗ).mp hEven a.2⟩
  have hbmem : b ∈ clusterKeptProductScope hPT M := by
    simpa [b, cₗ, hl'] using clusterKeptProductScope_contains_internal hPT hr l'
  have hbridge := clusterLabelFromInternal_internalNeighbor (hm := hm) I a l'
  have hbridge' := clusterLabelFromInternal_internalNeighbor (hm := hm) I' a l'
  calc
    (I s).2 (flipPos v.1 l) =
        clusterLabelFromInternal (hPT := hPT) hm I b := by
          simpa [s, v, hl'] using hbridge.symm
    _ = clusterLabelFromInternal (hPT := hPT) hm I' b := hlabels b hbmem
    _ = (I' s).2 (flipPos v.1 l) := by
          simpa [s, v, hl'] using hbridge'

theorem clusterKeptProduct_dependsOn_keptStarScope {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) :
    ClusterLabelDependsOn hPT hm
      (fun I => clusterKeptProduct PT hPT hm i x M W I)
      (clusterKeptProductScope hPT M) := by
  classical
  intro I I' hlabels
  unfold clusterKeptProduct
  apply congrArg₂ (fun p q : ℝ => p * q)
  · apply Finset.prod_congr rfl
    intro r hr
    apply congrArg₂ (fun p q : ℝ => p * q)
    · apply congrArg₂ (fun p q : ℝ => p * q)
      · rfl
      · exact clusterSigma_eq_of_keptStarLabels W I I' M r hr x hlabels
    · apply Finset.prod_congr rfl
      intro b hb
      apply congrArg (fun y => normalizedHit (T.S.E k) PT.tiling.c
        (PT.π (patchAt PT hPT b.1)) x y)
      have hmem : b ∈ clusterKeptProductScope hPT M :=
        clusterKeptProductScope_contains_bulk hPT hr hb
      exact hlabels b hmem
  · apply Finset.prod_congr rfl
    intro q hq
    apply congrArg (fun y =>
      (let d := deg (T.S.E k) PT.tiling.c
        (PT.π (patchAt PT hPT q.2.1)).w x
       if 0 < d then hit (T.S.E k) PT.tiling.c x y / d else 0))
    exact hlabels q.2 (clusterKeptProductScope_contains_crossing hPT hq)

private theorem normalizedHit_nonneg {N : ℕ} (E : Fin N → Fin N → Prop) (c : Colour)
    (π : Law N) (x y : Fin N) : 0 ≤ normalizedHit E c π x y := by
  dsimp [normalizedHit]
  split_ifs with hd
  · exact div_nonneg (by unfold hit; split_ifs <;> norm_num) (le_of_lt hd)
  · exact le_rfl

private theorem clusterSigma_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (a : EvenPosition T k) (x : Fin (T.S.N k)) : 0 ≤ clusterSigma PT hPT hm W I a x := by
  unfold clusterSigma
  exact (clusterSolver PT hPT hm (patchAt PT hPT a.1)).σ_nonneg
    (clusterCenterRole PT hPT hm a) (historyOnSlice W (clusterSliceAt PT hPT a.1))
    (nbrLabels (clusterCenterRole PT hPT hm a).1
      (I (clusterSliceAt PT hPT a.1)).2) x

private theorem clusterKeptProduct_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT) :
    0 ≤ clusterKeptProduct PT hPT hm i x M W I := by
  classical
  unfold clusterKeptProduct
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro r hr
    apply mul_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg _
      · exact clusterSigma_nonneg W I (M.positions r) x
    · apply Finset.prod_nonneg
      intro b hb
      exact normalizedHit_nonneg _ _ _ _ _
  · apply Finset.prod_nonneg
    intro q hq
    exact normalizedHit_nonneg _ _ _ _ _

theorem clusterSample_expect_disintegrate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm)
    (F : ((ClusterHistory PT hPT hm × ClusterBinAssignment PT) × ClusterInternalData PT) → ℝ) :
    CS.law.E (fun ω => F ((CS.history ω, CS.bins ω), CS.internal ω)) =
      CS.binStage.historyLaw.E (fun W => (CS.binStage.binLaw W).E (fun B =>
        (CS.labelKernel W B).E (fun I => F ((W, B), I)))) := by
  classical
  let f : CS.Outcome → (ClusterHistory PT hPT hm × ClusterBinAssignment PT) ×
      ClusterInternalData PT := fun ω => ((CS.history ω, CS.bins ω), CS.internal ω)
  calc
    CS.law.E (fun ω => F (f ω)) = (FinLaw.map CS.law f).E F :=
      (expect_map CS.law f F).symm
    _ = (FinLaw.bind (FinLaw.bind CS.binStage.historyLaw CS.binStage.binLaw)
        (fun wb => CS.labelKernel wb.1 wb.2)).E F := by rw [CS.label_disintegration]
    _ = CS.binStage.historyLaw.E (fun W => (CS.binStage.binLaw W).E (fun B =>
        (CS.labelKernel W B).E (fun I => F ((W, B), I)))) := by
      rw [expect_bind, expect_bind]

theorem clusterMaskedIntegral_disintegrate {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) :
    clusterMaskedIntegral CS i x M = CS.binStage.historyLaw.E (fun W =>
      if clusterHistoryLoad PT hPT hm W then
        (CS.binStage.binLaw W).E (fun B =>
          if ClusterMaskConsistent PT hPT hm M B then
            (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0)
      else 0) := by
  classical
  let F : ((ClusterHistory PT hPT hm × ClusterBinAssignment PT) ×
      ClusterInternalData PT) → ℝ := fun wbI =>
    if clusterHistoryLoad PT hPT hm wbI.1.1 ∧
        ClusterMaskConsistent PT hPT hm M wbI.1.2 then
      clusterKeptProduct PT hPT hm i x M wbI.1.1 wbI.2 else 0
  unfold clusterMaskedIntegral
  calc
    CS.law.E (fun ω => if CS.historyLoad ω ∧
        ClusterMaskConsistent PT hPT hm M (CS.bins ω) then
        clusterKeptProduct PT hPT hm i x M (CS.history ω) (CS.internal ω) else 0) =
      CS.law.E (fun ω => F ((CS.history ω, CS.bins ω), CS.internal ω)) := by
        unfold FinLaw.E
        apply Finset.sum_congr rfl
        intro ω hω
        simp [F, CS.history_eq ω]
    _ = CS.binStage.historyLaw.E (fun W => (CS.binStage.binLaw W).E (fun B =>
        (CS.labelKernel W B).E (fun I => F ((W, B), I)))) :=
      clusterSample_expect_disintegrate CS F
    _ = CS.binStage.historyLaw.E (fun W =>
        if clusterHistoryLoad PT hPT hm W then
          (CS.binStage.binLaw W).E (fun B =>
            if ClusterMaskConsistent PT hPT hm M B then
              (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0)
        else 0) := by
          apply congrArg
          funext W
          by_cases hload : clusterHistoryLoad PT hPT hm W
          · have hinner : ∀ B,
                (CS.labelKernel W B).E (fun I =>
                  if ClusterMaskConsistent PT hPT hm M B then
                    clusterKeptProduct PT hPT hm i x M W I else 0) =
                if ClusterMaskConsistent PT hPT hm M B then
                  (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0 := by
              intro B
              by_cases hmask : ClusterMaskConsistent PT hPT hm M B <;>
                simp [FinLaw.E, hmask]
            simpa [F, hload] using
              congrArg (CS.binStage.binLaw W).E (funext hinner)
          · simp [F, hload, FinLaw.E]

theorem clusterMaskedIntegral_le_of_labelComparison {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m) (x : Fin (T.S.N k))
    (M : ClusterMask PT) (C : ℝ)
    (hcmp : ∀ W, CS.binStage.historyLaw.w W ≠ 0 →
      clusterHistoryLoad PT hPT hm W → ∀ B, (CS.binStage.binLaw W).w B ≠ 0 →
      ClusterMaskConsistent PT hPT hm M B →
        (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) ≤
          C * (clusterIndependentLabelKernel PT hPT hm W B).E
            (clusterKeptProduct PT hPT hm i x M W)) :
    clusterMaskedIntegral CS i x M ≤ C * clusterAfterLabelIntegral CS i x M := by
  classical
  rw [clusterMaskedIntegral_disintegrate]
  unfold clusterAfterLabelIntegral
  have hlabel : ∀ W, CS.binStage.historyLaw.w W ≠ 0 →
      clusterHistoryLoad PT hPT hm W → ∀ B, (CS.binStage.binLaw W).w B ≠ 0 →
      (if ClusterMaskConsistent PT hPT hm M B then
        (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0) ≤
      C * (if ClusterMaskConsistent PT hPT hm M B then
        (clusterIndependentLabelKernel PT hPT hm W B).E
          (clusterKeptProduct PT hPT hm i x M W) else 0) := by
    intro W hW hload B hB
    by_cases hmask : ClusterMaskConsistent PT hPT hm M B
    · simpa [hmask] using hcmp W hW hload B hB hmask
    · simp [hmask]
  unfold FinLaw.E
  calc
    (∑ W, CS.binStage.historyLaw.w W *
        (if clusterHistoryLoad PT hPT hm W then
          ∑ B, (CS.binStage.binLaw W).w B *
            (if ClusterMaskConsistent PT hPT hm M B then
              (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0)
        else 0)) ≤
      ∑ W, C * (CS.binStage.historyLaw.w W *
        (if clusterHistoryLoad PT hPT hm W then
          ∑ B, (CS.binStage.binLaw W).w B *
            (if ClusterMaskConsistent PT hPT hm M B then
              (clusterIndependentLabelKernel PT hPT hm W B).E
                (clusterKeptProduct PT hPT hm i x M W) else 0)
        else 0)) := by
        apply Finset.sum_le_sum
        intro W hWmem
        by_cases hW : CS.binStage.historyLaw.w W = 0
        · simp [hW]
        · by_cases hload : clusterHistoryLoad PT hPT hm W
          · simp only [if_pos hload]
            have hbin : (∑ B, (CS.binStage.binLaw W).w B *
                (if ClusterMaskConsistent PT hPT hm M B then
                  (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0)) ≤
              C * (∑ B, (CS.binStage.binLaw W).w B *
                (if ClusterMaskConsistent PT hPT hm M B then
                  (clusterIndependentLabelKernel PT hPT hm W B).E
                    (clusterKeptProduct PT hPT hm i x M W) else 0)) := by
              calc
                _ ≤ ∑ B, C * ((CS.binStage.binLaw W).w B *
                    (if ClusterMaskConsistent PT hPT hm M B then
                      (clusterIndependentLabelKernel PT hPT hm W B).E
                        (clusterKeptProduct PT hPT hm i x M W) else 0)) := by
                  apply Finset.sum_le_sum
                  intro B hBmem
                  by_cases hB : (CS.binStage.binLaw W).w B = 0
                  · simp [hB]
                  · calc
                      (CS.binStage.binLaw W).w B *
                          (if ClusterMaskConsistent PT hPT hm M B then
                            (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0) ≤
                        (CS.binStage.binLaw W).w B * (C *
                          (if ClusterMaskConsistent PT hPT hm M B then
                            (clusterIndependentLabelKernel PT hPT hm W B).E
                              (clusterKeptProduct PT hPT hm i x M W) else 0)) :=
                        mul_le_mul_of_nonneg_left (hlabel W hW hload B hB)
                          ((CS.binStage.binLaw W).nonneg B)
                      _ = C * ((CS.binStage.binLaw W).w B *
                          (if ClusterMaskConsistent PT hPT hm M B then
                            (clusterIndependentLabelKernel PT hPT hm W B).E
                              (clusterKeptProduct PT hPT hm i x M W) else 0)) := by ring
                _ = C * (∑ B, (CS.binStage.binLaw W).w B *
                    (if ClusterMaskConsistent PT hPT hm M B then
                      (clusterIndependentLabelKernel PT hPT hm W B).E
                        (clusterKeptProduct PT hPT hm i x M W) else 0)) := by rw [Finset.mul_sum]
            have hWnonneg := CS.binStage.historyLaw.nonneg W
            calc
              CS.binStage.historyLaw.w W *
                  (∑ B, (CS.binStage.binLaw W).w B *
                    (if ClusterMaskConsistent PT hPT hm M B then
                      (CS.labelKernel W B).E (clusterKeptProduct PT hPT hm i x M W) else 0)) ≤
                CS.binStage.historyLaw.w W * (C * (∑ B, (CS.binStage.binLaw W).w B *
                    (if ClusterMaskConsistent PT hPT hm M B then
                      (clusterIndependentLabelKernel PT hPT hm W B).E
                        (clusterKeptProduct PT hPT hm i x M W) else 0))) :=
                mul_le_mul_of_nonneg_left hbin hWnonneg
              _ = C * (CS.binStage.historyLaw.w W *
                  (∑ B, (CS.binStage.binLaw W).w B *
                    (if ClusterMaskConsistent PT hPT hm M B then
                      (clusterIndependentLabelKernel PT hPT hm W B).E
                        (clusterKeptProduct PT hPT hm i x M W) else 0))) := by ring
          · simp [hload]
    _ = C * (∑ W, CS.binStage.historyLaw.w W *
        (if clusterHistoryLoad PT hPT hm W then
          ∑ B, (CS.binStage.binLaw W).w B *
            (if ClusterMaskConsistent PT hPT hm M B then
              (clusterIndependentLabelKernel PT hPT hm W B).E
                (clusterKeptProduct PT hPT hm i x M W) else 0)
        else 0)) := by rw [Finset.mul_sum]

theorem clusterLabelKernel_le_of_localComparisons {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (W : ClusterHistory PT hPT hm)
    (hW : CS.binStage.historyLaw.w W ≠ 0) (hload : clusterHistoryLoad PT hPT hm W)
    (B : ClusterBinAssignment PT) (hB : (CS.binStage.binLaw W).w B ≠ 0)
    (F : ClusterInternalData PT → ℝ) (S : Finset (OddPosition T k)) (E : ℝ)
    (hF : ∀ I, 0 ≤ F I)
    (hdep : ClusterLabelDependsOn hPT hm F S)
    (hcard : (S.card : ℝ) ≤ (T.S.n k : ℝ) ^ 2)
    (hquery : ClusterLabelQueryOK PT hPT hm B S)
    (herror : clusterLabelError PT hPT hm B S ≤ E) :
    (CS.labelKernel W B).E F ≤
      2 * E * (clusterIndependentLabelKernel PT hPT hm W B).E F := by
  have hlabel := CS.label_local_upper_comparison W hW hload B hB F hF S hdep hcard
  have hpre := CS.prelabel_upper_comparison W hW hload B hB F hF S hdep hcard hquery
  have hInd : 0 ≤ (clusterIndependentLabelKernel PT hPT hm W B).E F := by
    unfold FinLaw.E
    exact Finset.sum_nonneg fun I _ =>
      mul_nonneg ((clusterIndependentLabelKernel PT hPT hm W B).nonneg I) (hF I)
  calc
    (CS.labelKernel W B).E F ≤ 2 * (CS.preLabelKernel W B).E F := hlabel
    _ ≤ 2 * (clusterLabelError PT hPT hm B S *
        (clusterIndependentLabelKernel PT hPT hm W B).E F) :=
      mul_le_mul_of_nonneg_left hpre (by norm_num)
    _ ≤ 2 * E * (clusterIndependentLabelKernel PT hPT hm W B).E F := by
      have he := mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 2)
      calc
        2 * (clusterLabelError PT hPT hm B S *
            (clusterIndependentLabelKernel PT hPT hm W B).E F) =
          (2 * clusterLabelError PT hPT hm B S) *
            (clusterIndependentLabelKernel PT hPT hm W B).E F := by ring
        _ ≤ (2 * E) * (clusterIndependentLabelKernel PT hPT hm W B).E F :=
          mul_le_mul_of_nonneg_right he hInd
        _ = 2 * E * (clusterIndependentLabelKernel PT hPT hm W B).E F := by ring

private theorem clusterUnremovedCrossing_equal_bin_eq_role {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {M : ClusterMask PT} (B : ClusterBinAssignment PT)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    {q q' : Fin (T.S.n k) × OddPosition T k}
    (hq : q ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins)
    (hq' : q' ∈ clusterAllowedCrossings PT hPT M \ M.crossingBins)
    (hbin : (B (clusterGroupIndexAt PT hPT hm q.2)).1 =
      (B (clusterGroupIndexAt PT hPT hm q'.2)).1) : q.2 = q'.2 := by
  by_contra hrole
  have horderNe : clusterQueryOrder q ≠ clusterQueryOrder q' := by
    intro hEq
    have hpair := clusterQueryOrder_injective hEq
    exact hrole (congrArg Prod.snd hpair)
  rcases lt_or_gt_of_ne horderNe with hlt | hgt
  · exact (clusterConsistent_no_unremoved_crossing_repeat M B hsmall hcons
      (Finset.mem_sdiff.mp hq).1 hq' hlt) hbin
  · exact (clusterConsistent_no_unremoved_crossing_repeat M B hsmall hcons
      (Finset.mem_sdiff.mp hq').1 hq hgt) hbin.symm

private theorem clusterPatch_eq_of_coreGroup_mem {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {M : ClusterMask PT} {r : Fin (T.S.n k)} {b : OddPosition T k}
    (hg : clusterGroupIndexAt PT hPT hm b ∈ clusterCoreGroups PT hPT hm (M.positions r)) :
    patchAt PT hPT b.1 = patchAt PT hPT (M.positions r).1 := by
  classical
  unfold clusterCoreGroups at hg
  obtain ⟨c, hc, hcg⟩ := Finset.mem_image.mp hg
  have hpatchRow := (Finset.mem_filter.mp hc).2.2
  have hpatchGroup : patchAt PT hPT c.1 = patchAt PT hPT b.1 := by
    have hs := congrArg (fun g : ClusterGroupIndex PT => g.1.1) hcg
    simpa [clusterGroupIndexAt, clusterSliceAt] using hs
  exact hpatchGroup.symm.trans hpatchRow

private theorem clusterAdjacent_eq_flip {κ : CConsts} {T : Stage} {k : ℕ}
    {a : EvenPosition T k} {b : OddPosition T k}
    (hAdj : Adjacent a b) :
    ∃ j : Fin (T.S.n k), b.1 = flipPos a.1 j := by
  classical
  have hdiff : (Finset.univ.filter fun j : Fin (T.S.n k) => a.1 j ≠ b.1 j).card = 1 := hAdj
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hdiff
  have hjmem : j ∈ Finset.univ.filter fun j : Fin (T.S.n k) => a.1 j ≠ b.1 j := by
    rw [hj]
    simp
  have hdiffj : a.1 j ≠ b.1 j := (Finset.mem_filter.mp hjmem).2
  have hsame : ∀ t : Fin (T.S.n k), t ≠ j → a.1 t = b.1 t := by
    intro t ht
    have hnot : t ∉ Finset.univ.filter fun t : Fin (T.S.n k) => a.1 t ≠ b.1 t := by
      rw [hj]
      simp [ht]
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  refine ⟨j, ?_⟩
  funext t
  by_cases ht : t = j
  · subst t
    cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [flipPos]
  · simp [flipPos, ht, hsame t ht]

private theorem clusterHeq_fun_apply {n m : ℕ} (hnm : n = m)
    {f : CubePos n} {g : CubePos m} (hfg : HEq f g) (j : Fin n) :
    f j = g (Fin.cast hnm j) := by
  cases hnm
  exact congrFun (eq_of_heq hfg) j

private theorem clusterAdjacent_same_externalSlice_eq {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {a : EvenPosition T k} {b b' : OddPosition T k}
    (hAdj : Adjacent a b) (hAdj' : Adjacent a b')
    (hpatch : patchAt PT hPT b.1 = patchAt PT hPT a.1)
    (hpatch' : patchAt PT hPT b'.1 = patchAt PT hPT a.1)
    (hs : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT b'.1)
    (hsne : clusterSliceAt PT hPT b.1 ≠ clusterSliceAt PT hPT a.1) : b = b' := by
  classical
  obtain ⟨j, hflip⟩ := clusterAdjacent_eq_flip (κ := κ) hAdj
  obtain ⟨j', hflip'⟩ := clusterAdjacent_eq_flip (κ := κ) hAdj'
  have hsne' : clusterSliceAt PT hPT b'.1 ≠ clusterSliceAt PT hPT a.1 := by
    intro hs'
    exact hsne (hs.trans hs')
  have hjExternal : j.val < T.S.n k -
      (PT.tiling.P (patchAt PT hPT a.1)).h := by
    by_contra hj
    let l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h :=
      ⟨j.val - (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h), by
        have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1)
        omega⟩
    have hcoord : j = ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
        by
          have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1)
          have hl := l.isLt
          omega⟩ := by
      apply Fin.ext
      dsimp [l]
      omega
    have hslice := clusterSliceAt_flip_internal PT hPT a.1 l
    have hrowSlice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT a.1 := by
      rw [hflip, hcoord]
      exact hslice
    exact hsne hrowSlice
  have hj'External : j'.val < T.S.n k -
      (PT.tiling.P (patchAt PT hPT a.1)).h := by
    by_contra hj
    let l : Fin (PT.tiling.P (patchAt PT hPT a.1)).h :=
      ⟨j'.val - (T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h), by
        have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1)
        omega⟩
    have hcoord : j' = ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT a.1)).h + l.val,
        by
          have hh := clusterHeight_le PT hPT (patchAt PT hPT a.1)
          have hl := l.isLt
          omega⟩ := by
      apply Fin.ext
      dsimp [l]
      omega
    have hslice := clusterSliceAt_flip_internal PT hPT a.1 l
    have hrowSlice : clusterSliceAt PT hPT b'.1 = clusterSliceAt PT hPT a.1 := by
      rw [hflip', hcoord]
      exact hslice
    exact hsne' hrowSlice
  have hpatchBB' : patchAt PT hPT b.1 = patchAt PT hPT b'.1 := hpatch.trans hpatch'.symm
  have hdim : T.S.n k - (PT.tiling.P (patchAt PT hPT b.1)).h =
      T.S.n k - (PT.tiling.P (patchAt PT hPT b'.1)).h :=
    congrArg (fun p : Fin PT.tiling.m => T.S.n k - (PT.tiling.P p).h) hpatchBB'
  have hjExternalB : j.val < T.S.n k -
      (PT.tiling.P (patchAt PT hPT b.1)).h := by
    rw [hpatch]
    exact hjExternal
  have hjExternalB' : j.val < T.S.n k -
      (PT.tiling.P (patchAt PT hPT b'.1)).h := by omega
  have hout : HEq (outsideWord PT hPT (patchAt PT hPT b.1) b.1)
      (outsideWord PT hPT (patchAt PT hPT b'.1) b'.1) :=
    cluster_heq_of_dependent_apply (fun s : ClusterSlice PT => s.2.1) hs
  let jOut : Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT b.1)).h) :=
    ⟨j.val, hjExternalB⟩
  have houtj := clusterHeq_fun_apply hdim hout jOut
  have hcast : Fin.cast hdim jOut =
      (⟨j.val, hjExternalB'⟩ : Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT b'.1)).h)) := by
    apply Fin.ext
    rfl
  rw [hcast] at houtj
  have hcoord : b.1 j = b'.1 j := by
    simpa [outsideWord, jOut] using houtj
  have hjj : j = j' := by
    by_contra hne
    rw [hflip, hflip'] at hcoord
    cases hrow : a.1 j <;> simp [flipPos, hne, hrow] at hcoord
  apply Subtype.ext
  rw [hflip, hflip', hjj]

private noncomputable def clusterInternalStarNeighbor {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (M : ClusterMask PT)
    (r : Fin (T.S.n k))
    (l : Fin (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h) : OddPosition T k :=
  ⟨flipPos (M.positions r).1
      ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h + l.val,
        by
          have hh := clusterHeight_le PT hPT (patchAt PT hPT (M.positions r).1)
          have hl := l.isLt
          omega⟩,
    by
      intro hEven
      exact (evenRole_flipPos (M.positions r).1
        ⟨T.S.n k - (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h + l.val,
          by
            have hh := clusterHeight_le PT hPT (patchAt PT hPT (M.positions r).1)
            have hl := l.isLt
            omega⟩).mp hEven (M.positions r).2⟩

private noncomputable def clusterInternalStarRoles {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (M : ClusterMask PT)
    (r : Fin (T.S.n k)) : Finset (OddPosition T k) :=
  (Finset.univ : Finset (Fin (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h)).image
    (clusterInternalStarNeighbor hPT M r)

private theorem clusterInternalStarRoles_card_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (hPT : PT.Valid) (M : ClusterMask PT)
    (r : Fin (T.S.n k)) :
    (clusterInternalStarRoles hPT M r).card ≤
      (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h := by
  classical
  unfold clusterInternalStarRoles
  calc
    _ ≤ (Finset.univ : Finset
      (Fin (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h)).card := Finset.card_image_le
    _ = (PT.tiling.P (patchAt PT hPT (M.positions r).1)).h := by simp

private theorem clusterFinite_sum_biUnion_le {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤ ∑ a ∈ s, ∑ x ∈ t a, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert]
    have hdisj : Disjoint (t a) ((s.biUnion t) \ t a) := disjoint_sdiff_self_right
    have hunion : t a ∪ ((s.biUnion t) \ t a) = t a ∪ s.biUnion t :=
      Finset.union_sdiff_self_eq_union
    calc
      (∑ x ∈ t a ∪ s.biUnion t, f x) =
          ∑ x ∈ t a ∪ ((s.biUnion t) \ t a), f x := by rw [hunion]
      _ = (∑ x ∈ t a, f x) + ∑ x ∈ (s.biUnion t) \ t a, f x := by
        rw [Finset.sum_union hdisj]
      _ ≤ (∑ x ∈ t a, f x) + ∑ x ∈ s.biUnion t, f x := by
        apply add_le_add_right
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.sdiff_subset
        · intro x hx hxnot
          exact hf x
      _ ≤ (∑ x ∈ t a, f x) + ∑ a' ∈ s, ∑ x ∈ t a', f x :=
        add_le_add_right ih _
      _ = ∑ a' ∈ insert a s, ∑ x ∈ t a', f x := by simp [ha]

private theorem clusterAdjacent_sameSlice_mem_internalStarRoles {κ : CConsts}
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {M : ClusterMask PT} {r : Fin (T.S.n k)} {b : OddPosition T k}
    (hAdj : Adjacent (M.positions r) b)
    (hs : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT (M.positions r).1) :
    b ∈ clusterInternalStarRoles hPT M r := by
  classical
  let a := M.positions r
  let i := patchAt PT hPT a.1
  obtain ⟨j, hflip⟩ := clusterAdjacent_eq_flip (κ := κ) hAdj
  by_cases hj : T.S.n k - (PT.tiling.P i).h ≤ j.val
  · let l : Fin (PT.tiling.P i).h := ⟨j.val - (T.S.n k - (PT.tiling.P i).h), by
      have hh := clusterHeight_le PT hPT i
      omega⟩
    have hcoord : j = ⟨T.S.n k - (PT.tiling.P i).h + l.val,
        by
          have hh := clusterHeight_le PT hPT i
          have hl := l.isLt
          omega⟩ := by
      apply Fin.ext
      dsimp [l]
      omega
    have hneighbor : b.1 = flipPos a.1
        ⟨T.S.n k - (PT.tiling.P i).h + l.val,
          by
            have hh := clusterHeight_le PT hPT i
            have hl := l.isLt
            omega⟩ := by
      calc
        b.1 = flipPos a.1 j := hflip
        _ = flipPos a.1 ⟨T.S.n k - (PT.tiling.P i).h + l.val, by
            have hh := clusterHeight_le PT hPT i
            have hl := l.isLt
            omega⟩ := congrArg (flipPos a.1) hcoord
    apply Finset.mem_image.mpr
    refine ⟨l, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    simpa [clusterInternalStarNeighbor, i, a] using hneighbor.symm
  · have hjExternal : j.val < T.S.n k - (PT.tiling.P i).h := by omega
    have hpatch : patchAt PT hPT b.1 = i := congrArg Sigma.fst hs
    have hdim : T.S.n k - (PT.tiling.P (patchAt PT hPT b.1)).h =
        T.S.n k - (PT.tiling.P i).h := by rw [hpatch]
    have hout : HEq (outsideWord PT hPT (patchAt PT hPT b.1) b.1)
        (outsideWord PT hPT i a.1) :=
      cluster_heq_of_dependent_apply (fun s : ClusterSlice PT => s.2.1) hs
    let jOut : Fin (T.S.n k - (PT.tiling.P (patchAt PT hPT b.1)).h) :=
      ⟨j.val, by simpa [hpatch] using hjExternal⟩
    have houtj := clusterHeq_fun_apply hdim hout jOut
    have hcast : Fin.cast hdim jOut =
        (⟨j.val, hjExternal⟩ : Fin (T.S.n k - (PT.tiling.P i).h)) := by
      apply Fin.ext
      rfl
    rw [hcast] at houtj
    have hcoord : b.1 j = a.1 j := by
      simpa [outsideWord, jOut] using houtj
    rw [hflip] at hcoord
    cases ha : a.1 j <;> simp [a, flipPos, ha] at hcoord

theorem clusterKeptProductScope_equal_bin_classification {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {i : Fin PT.tiling.m} {M : ClusterMask PT} {W : ClusterHistory PT hPT hm}
    (hGeom : ClusterMaskGeometry PT hPT i M) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    {b b' : OddPosition T k}
    (hb : b ∈ clusterKeptProductScope hPT M)
    (hb' : b' ∈ clusterKeptProductScope hPT M)
    (hbin : (B (clusterGroupIndexAt PT hPT hm b)).1 =
      (B (clusterGroupIndexAt PT hPT hm b')).1) :
    b = b' ∨ ∃ r, r ∈ clusterKeptRows M ∧
      Adjacent (M.positions r) b ∧ Adjacent (M.positions r) b' ∧
      clusterGroupIndexAt PT hPT hm b = clusterGroupIndexAt PT hPT hm b' ∧
      patchAt PT hPT b.1 = patchAt PT hPT (M.positions r).1 ∧
      patchAt PT hPT b'.1 = patchAt PT hPT (M.positions r).1 := by
  classical
  rcases clusterKeptProductScope_core_or_crossing hb with
    ⟨r, hr, hAdj, hg⟩ | ⟨q, hqrow, hAdj, hq⟩
  · rcases clusterKeptProductScope_core_or_crossing hb' with
      ⟨t, ht, hAdj', hg'⟩ | ⟨q, hqrow, hAdj', hq⟩
    · have hstarDistinct : ∀ a b b', Adjacent a b → Adjacent a b' →
          clusterGroupIndexAt PT hPT hm b ≠ clusterGroupIndexAt PT hPT hm b' →
            (B (clusterGroupIndexAt PT hPT hm b)).1 ≠
              (B (clusterGroupIndexAt PT hPT hm b')).1 := by
        intro a b₁ b₂ ha₁ ha₂ hneq
        exact clusterBinGood_separates_star_groups W B hgood hsmall ha₁ ha₂ hneq
      have hsame := coreGroup_bin_eq_for_kept_rows_same_row M B hsmall hcons
        hstarDistinct hr ht hg hg' hbin
      have hpatchB := clusterPatch_eq_of_coreGroup_mem hg
      have hpatchB' := clusterPatch_eq_of_coreGroup_mem hg'
      rcases hsame with ⟨hrt, hgroups⟩
      subst t
      exact Or.inr ⟨r, hr, hAdj, hAdj', hgroups, hpatchB, hpatchB'⟩
    · have hcross := (Finset.mem_sdiff.mp hq).1
      have hne := clusterCore_crossing_bins_neq hGeom hr hg hcross
        (B (clusterGroupIndexAt PT hPT hm b)) (B (clusterGroupIndexAt PT hPT hm b'))
      exact (hne hbin).elim
  · rcases clusterKeptProductScope_core_or_crossing hb' with
      ⟨t, ht, hAdj', hg'⟩ | ⟨q', hqrow', hAdj', hq'⟩
    · have hcross := (Finset.mem_sdiff.mp hq).1
      have hne := clusterCore_crossing_bins_neq hGeom ht hg' hcross
        (B (clusterGroupIndexAt PT hPT hm b')) (B (clusterGroupIndexAt PT hPT hm b))
      exact (hne hbin.symm).elim
    · have hrole := clusterUnremovedCrossing_equal_bin_eq_role B hsmall hcons hq hq' hbin
      exact Or.inl hrole

theorem clusterKeptProductScope_binQueryCount_le_twiceHeight {κ : CConsts}
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {i : Fin PT.tiling.m} {M : ClusterMask PT} {W : ClusterHistory PT hPT hm}
    (hGeom : ClusterMaskGeometry PT hPT i M) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    {b : OddPosition T k} (hb : b ∈ clusterKeptProductScope hPT M) :
    clusterBinQueryCount PT hPT hm B (clusterKeptProductScope hPT M) b ≤
      2 * (PT.tiling.P (patchAt PT hPT b.1)).h := by
  classical
  let S := clusterKeptProductScope hPT M
  let Q : Finset (OddPosition T k) := S.filter fun b' =>
    (B (clusterGroupIndexAt PT hPT hm b')).1 =
      (B (clusterGroupIndexAt PT hPT hm b)).1
  have hQmap : ∀ b' ∈ Q,
      clusterSliceWord hPT b' ∈
        clusterGroupWordChoices hPT hm (clusterGroupIndexAt PT hPT hm b) := by
    intro b' hb'
    have hb'S : b' ∈ S := (Finset.mem_filter.mp hb').1
    have hbin := (Finset.mem_filter.mp hb').2
    rcases clusterKeptProductScope_equal_bin_classification hGeom B hgood hsmall hcons
        hb hb'S hbin.symm with hEq | ⟨r, hr, hAdj, hAdj', hgroups, _, _⟩
    · subst b'
      exact clusterSliceWord_mem_groupChoices (hPT := hPT) (hm := hm) b
    · have hgroups' : clusterGroupIndexAt PT hPT hm b' =
          clusterGroupIndexAt PT hPT hm b := hgroups.symm
      have hmem := clusterSliceWord_mem_groupChoices (hPT := hPT) (hm := hm) b'
      rw [hgroups'] at hmem
      exact hmem
  have hsubset : Q.image (clusterSliceWord hPT) ⊆
      clusterGroupWordChoices hPT hm (clusterGroupIndexAt PT hPT hm b) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨b', hb', rfl⟩
    exact hQmap b' hb'
  have hinj : Set.InjOn (clusterSliceWord hPT) Q :=
    (clusterSliceWord_injective hPT).injOn
  have hcardImage : (Q.image (clusterSliceWord hPT)).card = Q.card :=
    Finset.card_image_iff.mpr hinj
  change Q.card ≤ 2 * (PT.tiling.P (patchAt PT hPT b.1)).h
  calc
    Q.card = (Q.image (clusterSliceWord hPT)).card := hcardImage.symm
    _ ≤ (clusterGroupWordChoices hPT hm (clusterGroupIndexAt PT hPT hm b)).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 * (PT.tiling.P (clusterGroupIndexAt PT hPT hm b).1.1).h :=
      clusterGroupWordChoices_card_le (hPT := hPT) (hm := hm)
        (clusterGroupIndexAt PT hPT hm b)
    _ = 2 * (PT.tiling.P (patchAt PT hPT b.1)).h := by rfl

theorem clusterHighSmall_height_degree_scale {κ : CConsts} (hκ : κ.Admissible)
    (T : Stage) :
    ∀ᶠ k in atTop, ∀ 𝒯 : Tiling κ T k, Tiling.Valid 𝒯 →
      𝒯.mode = .highSmall → ∀ i,
        ((𝒯.P i).h : ℝ) ≤ ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) ∧
        2 * ((𝒯.P i).h : ℝ) ≤ ((𝒯.P i).d : ℝ) ^ (0.025 : ℝ) ∧
        ((𝒯.P i).h : ℝ) * ((𝒯.P i).d : ℝ) ^ (-0.04 : ℝ) ≤ 1 := by
  have hMhi : 0 < (κ.Mhi : ℝ) := by
    have hnonneg : 0 ≤ (κ.Mhi : ℝ) := Nat.cast_nonneg _
    nlinarith [hκ.Mhi_big.2, hκ.cq_rng.1]
  have hCb : 100 < κ.Cb := by
    have hratio : 0 < κ.aC / κ.aB := div_pos hκ.aC_rng.1 hκ.aB_rng.1
    have hterm : 0 < 100 * (κ.aC / κ.aB) := by positivity
    have hCbBig := hκ.Cb_big
    have hEq : (100 : ℝ) * κ.aC / κ.aB = 100 * (κ.aC / κ.aB) := by ring
    rw [hEq] at hCbBig
    linarith
  have hMlo : 0 < κ.Mlo := by
    have hMloR : (0 : ℝ) < (κ.Mlo : ℝ) := by linarith [hCb, hκ.Mlo_big]
    exact_mod_cast hMloR
  have hMloCast : 1 ≤ (κ.Mlo : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hMlo))
  have hcqHalf : κ.cq < 1 / 2 := by
    have hden : 2 < 20 * (κ.Mlo : ℝ) := by nlinarith
    have hfrac : 1 / (20 * (κ.Mlo : ℝ)) < (1 / 2 : ℝ) :=
      one_div_lt_one_div_of_lt (by norm_num) hden
    exact hκ.cq_rng.2.trans hfrac
  let logN : ℕ → ℝ := fun k => Real.log (T.S.n k : ℝ)
  have hn : Tendsto (fun k => (T.S.n k : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have ht : Tendsto logN atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hu : Tendsto (fun k => logN k ^ κ.cq) atTop atTop :=
    (tendsto_rpow_atTop hκ.cq_rng.1).comp ht
  let s : ℝ := 2 * (κ.Mhi : ℝ) / κ.cq
  have hRatio : Tendsto (fun k => Real.exp (0.0025 * (logN k ^ κ.cq)) /
      (logN k ^ κ.cq) ^ s) atTop atTop := by
    exact (tendsto_exp_mul_div_rpow_atTop s 0.0025 (by norm_num)).comp hu
  filter_upwards [hu.eventually_ge_atTop (2 ^ 60 : ℝ),
      ht.eventually_ge_atTop (1 : ℝ), hRatio.eventually_ge_atTop (4 : ℝ)]
      with k huk htk hratio
  intro 𝒯 h𝒯 hmode i
  rcases h𝒯.cluster_data (Or.inr (Or.inl hmode)) i with
    ⟨_, _, _, hdFormula, _, _, _, _, hhUpper, _, hsmallIff, _⟩
  have hdFormula' := hdFormula hmode
  have hsmallScale := hsmallIff.mp hmode
  rcases hsmallScale with ⟨hqLower, hqUpper⟩
  let t : ℝ := logN k
  let u : ℝ := t ^ κ.cq
  change (2 ^ 60 : ℝ) ≤ logN k ^ κ.cq at huk
  change 1 ≤ logN k at htk
  change 4 ≤ Real.exp (0.0025 * (logN k ^ κ.cq)) /
    (logN k ^ κ.cq) ^ s at hratio
  have hu2 : 2 ≤ u := by
    have h2 : (2 : ℝ) ≤ 2 ^ 60 := by norm_num
    simpa [u, t] using le_trans h2 huk
  have ht1 : 1 ≤ t := by simpa [t] using htk
  have hsqrt : u ≤ Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  have hqlo : u < (𝒯.P i).q := by simpa [u, t, logN] using hqLower
  have hqhi : (𝒯.P i).q ≤ t ^ 2 := by simpa [t, logN] using hqUpper
  have hqFloorArg : u / 2 ≤ (𝒯.P i).q / 2 := by linarith
  have hsqrtFloorArg : u / 2 ≤ Real.sqrt t := by linarith
  have hfloor1 : ⌊Real.exp (u / 2)⌋₊ ≤
      ⌊Real.exp ((𝒯.P i).q / 2)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hqFloorArg)
  have hfloor2 : ⌊Real.exp (u / 2)⌋₊ ≤
      ⌊Real.exp (Real.sqrt t)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr hsqrtFloorArg)
  have hfloorNat : ⌊Real.exp (u / 2)⌋₊ ≤ (𝒯.P i).d := by
    rw [hdFormula']
    exact Nat.le_min.mpr ⟨hfloor1, hfloor2⟩
  have hfloorReal : (⌊Real.exp (u / 2)⌋₊ : ℝ) ≤ (𝒯.P i).d := by
    exact_mod_cast hfloorNat
  have hexpLinear : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp _
  have hexpTwo : 2 ≤ Real.exp (u / 2) := by nlinarith [hu2, hexpLinear]
  have hfloorAdd : Real.exp (u / 2) < (⌊Real.exp (u / 2)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloorHalf : Real.exp (u / 2) / 2 ≤ (⌊Real.exp (u / 2)⌋₊ : ℝ) := by
    nlinarith [hexpTwo, hfloorAdd]
  have hdLower : Real.exp (u / 2) / 2 ≤ (𝒯.P i).d := hfloorHalf.trans hfloorReal
  have hheightUpper : ((𝒯.P i).h : ℝ) <
      2 * Real.rpow ((𝒯.P i).q : ℝ) (κ.Mhi : ℝ) := by
    simpa [hmode] using hhUpper
  have hqPower : Real.rpow ((𝒯.P i).q : ℝ) (κ.Mhi : ℝ) ≤
      Real.rpow t (2 * (κ.Mhi : ℝ)) := by
    calc
      _ ≤ Real.rpow (t ^ 2) (κ.Mhi : ℝ) :=
        Real.rpow_le_rpow (by positivity) hqhi (by positivity)
      _ = Real.rpow t (2 * (κ.Mhi : ℝ)) := by
        simpa [mul_comm] using
          (Real.rpow_mul (by positivity : 0 ≤ t) (2 : ℝ) (κ.Mhi : ℝ)).symm
  have huPower : Real.rpow t (2 * (κ.Mhi : ℝ)) = Real.rpow u s := by
    have hmul : κ.cq * s = 2 * (κ.Mhi : ℝ) := by
      dsimp [s]
      field_simp [hκ.cq_rng.1.ne']
    dsimp [u]
    rw [← Real.rpow_mul (by positivity : 0 ≤ t) κ.cq s, hmul]
  have hheightBound : ((𝒯.P i).h : ℝ) < 2 * Real.rpow u s := by
    calc
      _ < 2 * Real.rpow ((𝒯.P i).q : ℝ) (κ.Mhi : ℝ) := hheightUpper
      _ ≤ 2 * Real.rpow t (2 * (κ.Mhi : ℝ)) :=
        mul_le_mul_of_nonneg_left hqPower (by norm_num)
      _ = 2 * Real.rpow u s := by rw [huPower]
  have huPos : 0 < u := by linarith
  have huPowPos : 0 < Real.rpow u s := Real.rpow_pos_of_pos huPos _
  have hratioMul : 4 * Real.rpow u s ≤ Real.exp (0.0025 * u) :=
    (le_div_iff₀ huPowPos).mp (by simpa [u, t] using hratio)
  have hheightExp : ((𝒯.P i).h : ℝ) ≤ Real.exp (0.0025 * u) / 2 := by
    calc
      _ ≤ 2 * Real.rpow u s := le_of_lt hheightBound
      _ ≤ Real.exp (0.0025 * u) / 2 := by
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by nlinarith [hratioMul])
  have hpowLower : Real.exp (0.0025 * u) / 2 ≤
      ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) := by
    have hmono := Real.rpow_le_rpow (by positivity) hdLower (by norm_num : (0 : ℝ) ≤ 0.005)
    have hiden : (Real.exp (u / 2) / 2) ^ (0.005 : ℝ) =
        Real.exp (0.0025 * u) / (2 : ℝ) ^ (0.005 : ℝ) := by
      rw [Real.div_rpow (by positivity) (by norm_num : (0 : ℝ) ≤ 2)]
      calc
        _ = Real.exp ((u / 2) * (0.005 : ℝ)) / (2 : ℝ) ^ (0.005 : ℝ) := by
          rw [← Real.exp_mul]
        _ = Real.exp (0.0025 * u) / (2 : ℝ) ^ (0.005 : ℝ) := by congr 1 <;> ring
    have htwo : (2 : ℝ) ^ (0.005 : ℝ) ≤ 2 := by
      calc
        _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (y := (0.005 : ℝ))
            (z := (1 : ℝ)) (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one _
    have hfrac : Real.exp (0.0025 * u) / 2 ≤
        Real.exp (0.0025 * u) / (2 : ℝ) ^ (0.005 : ℝ) := by
      apply (div_le_div_iff₀ (by norm_num)
        (Real.rpow_pos_of_pos (by norm_num) _)).2
      exact mul_le_mul_of_nonneg_left htwo (le_of_lt (Real.exp_pos _))
    calc
      _ ≤ Real.exp (0.0025 * u) / (2 : ℝ) ^ (0.005 : ℝ) := hfrac
      _ = (Real.exp (u / 2) / 2) ^ (0.005 : ℝ) := hiden.symm
      _ ≤ ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) := hmono
  have hheightSmall : ((𝒯.P i).h : ℝ) ≤ ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) :=
    hheightExp.trans hpowLower
  have hdHuge : (2 : ℝ) ^ 50 ≤ (𝒯.P i).d := by
    have hlinear : u / 2 ≤ Real.exp (u / 2) := le_trans (by linarith) hexpLinear
    have hlarge : (2 : ℝ) ^ 50 ≤ u / 4 := by nlinarith [huk]
    calc
      _ ≤ u / 4 := hlarge
      _ ≤ Real.exp (u / 2) / 2 := by linarith
      _ ≤ (𝒯.P i).d := hdLower
  have hdPowTwo : (2 : ℝ) ≤ ((𝒯.P i).d : ℝ) ^ (0.02 : ℝ) := by
    have hbase : ((2 : ℝ) ^ 50) ^ (0.02 : ℝ) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      norm_num
    rw [← hbase]
    exact Real.rpow_le_rpow (by positivity) hdHuge (by norm_num : (0 : ℝ) ≤ 0.02)
  have hqueryFactor : 2 * ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) ≤
      ((𝒯.P i).d : ℝ) ^ (0.025 : ℝ) := by
    calc
      _ ≤ ((𝒯.P i).d : ℝ) ^ (0.02 : ℝ) *
          ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) :=
        mul_le_mul_of_nonneg_right hdPowTwo (by positivity)
      _ = ((𝒯.P i).d : ℝ) ^ (0.025 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        norm_num
  have hqueryHeight : 2 * ((𝒯.P i).h : ℝ) ≤
      ((𝒯.P i).d : ℝ) ^ (0.025 : ℝ) := by
    calc
      _ ≤ 2 * ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) :=
        mul_le_mul_of_nonneg_left hheightSmall (by norm_num)
      _ ≤ ((𝒯.P i).d : ℝ) ^ (0.025 : ℝ) := hqueryFactor
  have hheightError : ((𝒯.P i).h : ℝ) *
      ((𝒯.P i).d : ℝ) ^ (-0.04 : ℝ) ≤ 1 := by
    calc
      _ ≤ ((𝒯.P i).d : ℝ) ^ (0.005 : ℝ) *
          ((𝒯.P i).d : ℝ) ^ (-0.04 : ℝ) :=
        mul_le_mul_of_nonneg_right hheightSmall (by positivity)
      _ = ((𝒯.P i).d : ℝ) ^ (-0.035 : ℝ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        norm_num
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
        (le_trans (by norm_num : (1 : ℝ) ≤ 2 ^ 50) hdHuge) (by norm_num)
  exact ⟨hheightSmall, hqueryHeight, hheightError⟩

private noncomputable def clusterRepeatedScopeRoles {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (B : ClusterBinAssignment PT) (S : Finset (OddPosition T k)) :
    Finset (OddPosition T k) :=
  S.filter fun b => 2 ≤ clusterBinQueryCount PT hPT hm B S b

theorem clusterRepeatedProductRoles_subset_internalRows {κ : CConsts}
    {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {i : Fin PT.tiling.m} {M : ClusterMask PT} {W : ClusterHistory PT hPT hm}
    (hGeom : ClusterMaskGeometry PT hPT i M) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B) :
    clusterRepeatedScopeRoles (hPT := hPT) (hm := hm) B
        (clusterKeptProductScope hPT M) ⊆
      (clusterKeptRows M).biUnion (clusterInternalStarRoles hPT M) := by
  classical
  intro b hb
  have hbScope : b ∈ clusterKeptProductScope hPT M :=
    (Finset.mem_filter.mp hb).1
  have hrep : 2 ≤ clusterBinQueryCount PT hPT hm B (clusterKeptProductScope hPT M) b :=
    (Finset.mem_filter.mp hb).2
  let Q : Finset (OddPosition T k) :=
    (clusterKeptProductScope hPT M).filter fun b' =>
      (B (clusterGroupIndexAt PT hPT hm b')).1 =
        (B (clusterGroupIndexAt PT hPT hm b)).1
  have hbQ : b ∈ Q :=
    Finset.mem_filter.mpr ⟨hbScope, by rfl⟩
  have hQcard : 2 ≤ Q.card := by
    simpa [clusterBinQueryCount, Q] using hrep
  have hErase : 0 < (Q.erase b).card := by
    rw [Finset.card_erase_of_mem hbQ]
    omega
  obtain ⟨b', hb'Erase⟩ := Finset.card_pos.mp hErase
  have hb'Q : b' ∈ Q := Finset.mem_of_mem_erase hb'Erase
  have hne : b' ≠ b := (Finset.mem_erase.mp hb'Erase).1
  have hb'Scope : b' ∈ clusterKeptProductScope hPT M :=
    (Finset.mem_filter.mp hb'Q).1
  have hbinRev := (Finset.mem_filter.mp hb'Q).2
  rcases clusterKeptProductScope_equal_bin_classification hGeom B hgood hsmall hcons
      hbScope hb'Scope hbinRev.symm with
    hEq | ⟨r, hr, hAdj, hAdj', hgroups, hpatch, hpatch'⟩
  · exact (hne hEq.symm).elim
  · have hslice : clusterSliceAt PT hPT b.1 = clusterSliceAt PT hPT b'.1 :=
      congrArg Sigma.fst hgroups
    by_cases hsrow : clusterSliceAt PT hPT b.1 =
        clusterSliceAt PT hPT (M.positions r).1
    · exact Finset.mem_biUnion.mpr
        ⟨r, hr, clusterAdjacent_sameSlice_mem_internalStarRoles hAdj hsrow⟩
    · have hroles := clusterAdjacent_same_externalSlice_eq hAdj hAdj' hpatch hpatch' hslice hsrow
      exact (hne hroles.symm).elim

theorem clusterLabelErrorExponent_le_dimension {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {i : Fin PT.tiling.m} {M : ClusterMask PT} {W : ClusterHistory PT hPT hm}
    (hGeom : ClusterMaskGeometry PT hPT i M) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    (hscale : ∀ j, ((PT.tiling.P j).h : ℝ) ≤ ((PT.tiling.P j).d : ℝ) ^ (0.005 : ℝ) ∧
      2 * ((PT.tiling.P j).h : ℝ) ≤ ((PT.tiling.P j).d : ℝ) ^ (0.025 : ℝ) ∧
      ((PT.tiling.P j).h : ℝ) * ((PT.tiling.P j).d : ℝ) ^ (-0.04 : ℝ) ≤ 1) :
    (∑ b ∈ clusterKeptProductScope hPT M,
      if 2 ≤ clusterBinQueryCount PT hPT hm B (clusterKeptProductScope hPT M) b then
        ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ) else 0) ≤
      (T.S.n k : ℝ) := by
  classical
  let S := clusterKeptProductScope hPT M
  let U := clusterRepeatedScopeRoles (hPT := hPT) (hm := hm) B S
  let Irow := clusterInternalStarRoles hPT M
  let f : OddPosition T k → ℝ := fun b =>
    ((PT.tiling.P (patchAt PT hPT b.1)).d : ℝ) ^ (-0.04 : ℝ)
  have hsumEq : (∑ b ∈ S,
      if 2 ≤ clusterBinQueryCount PT hPT hm B S b then f b else 0) =
      ∑ b ∈ U, f b := by
    simp [U, clusterRepeatedScopeRoles, Finset.sum_filter, f]
  have hUsub : U ⊆ (clusterKeptRows M).biUnion Irow :=
    clusterRepeatedProductRoles_subset_internalRows hGeom B hgood hsmall hcons
  have hf : ∀ b, 0 ≤ f b := by intro b; dsimp [f]; positivity
  have hsumSubset : (∑ b ∈ U, f b) ≤
      ∑ b ∈ (clusterKeptRows M).biUnion Irow, f b :=
    Finset.sum_le_sum_of_subset_of_nonneg hUsub (by intro b hb hnot; exact hf b)
  have hsumPair : (∑ b ∈ (clusterKeptRows M).biUnion Irow, f b) ≤
      ∑ r ∈ clusterKeptRows M, ∑ b ∈ Irow r, f b :=
    clusterFinite_sum_biUnion_le (clusterKeptRows M) Irow f hf
  have hrowBound : ∀ r ∈ clusterKeptRows M, (∑ b ∈ Irow r, f b) ≤ 1 := by
    intro r hr
    let ir : Fin PT.tiling.m := patchAt PT hPT (M.positions r).1
    have hpatch : ∀ b ∈ Irow r, patchAt PT hPT b.1 = ir := by
      intro b hb
      unfold Irow clusterInternalStarRoles at hb
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hb
      simpa [ir, clusterInternalStarNeighbor] using patchAt_flip_internal PT hPT
        (M.positions r).1 l
    calc
      (∑ b ∈ Irow r, f b) = ∑ b ∈ Irow r,
          ((PT.tiling.P ir).d : ℝ) ^ (-0.04 : ℝ) := by
            apply Finset.sum_congr rfl
            intro b hb
            simp [f, hpatch b hb, ir]
      _ = (Irow r).card * ((PT.tiling.P ir).d : ℝ) ^ (-0.04 : ℝ) := by simp
      _ ≤ (PT.tiling.P ir).h * ((PT.tiling.P ir).d : ℝ) ^ (-0.04 : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast clusterInternalStarRoles_card_le hPT M r)
              (by positivity)
      _ ≤ 1 := (hscale ir).2.2
  have hsumRows : (∑ r ∈ clusterKeptRows M, ∑ b ∈ Irow r, f b) ≤
      (T.S.n k : ℝ) := by
    calc
      _ ≤ ∑ r ∈ clusterKeptRows M, (1 : ℝ) :=
        Finset.sum_le_sum fun r hr => hrowBound r hr
      _ = (clusterKeptRows M).card := by simp
      _ ≤ T.S.n k := by
        have hcard : (clusterKeptRows M).card ≤ T.S.n k := by
          simpa using Finset.card_le_univ (clusterKeptRows M)
        exact_mod_cast hcard
  calc
    _ = ∑ b ∈ U, f b := hsumEq
    _ ≤ ∑ b ∈ (clusterKeptRows M).biUnion Irow, f b := hsumSubset
    _ ≤ ∑ r ∈ clusterKeptRows M, ∑ b ∈ Irow r, f b := hsumPair
    _ ≤ (T.S.n k : ℝ) := hsumRows

theorem clusterKeptProductScope_labelQueryOK {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {i : Fin PT.tiling.m} {M : ClusterMask PT} {W : ClusterHistory PT hPT hm}
    (hGeom : ClusterMaskGeometry PT hPT i M) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    (hscale : ∀ j, 2 * ((PT.tiling.P j).h : ℝ) ≤
      ((PT.tiling.P j).d : ℝ) ^ (0.025 : ℝ)) :
    ClusterLabelQueryOK PT hPT hm B (clusterKeptProductScope hPT M) := by
  intro hmode b hb
  have hcount := clusterKeptProductScope_binQueryCount_le_twiceHeight
    hGeom B hgood hsmall hcons hb
  have hcountReal : (clusterBinQueryCount PT hPT hm B
      (clusterKeptProductScope hPT M) b : ℝ) ≤
      2 * ((PT.tiling.P (patchAt PT hPT b.1)).h : ℝ) := by
    exact_mod_cast hcount
  exact hcountReal.trans (hscale (patchAt PT hPT b.1))

theorem clusterLabelError_le_exp_dimension {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    {i : Fin PT.tiling.m} {M : ClusterMask PT} {W : ClusterHistory PT hPT hm}
    (hGeom : ClusterMaskGeometry PT hPT i M) (B : ClusterBinAssignment PT)
    (hgood : clusterBinGood PT hPT hm W B)
    (hsmall : PT.tiling.mode = .highSmall)
    (hcons : ClusterMaskConsistent PT hPT hm M B)
    (hscale : ∀ j, ((PT.tiling.P j).h : ℝ) ≤ ((PT.tiling.P j).d : ℝ) ^ (0.005 : ℝ) ∧
      2 * ((PT.tiling.P j).h : ℝ) ≤ ((PT.tiling.P j).d : ℝ) ^ (0.025 : ℝ) ∧
      ((PT.tiling.P j).h : ℝ) * ((PT.tiling.P j).d : ℝ) ^ (-0.04 : ℝ) ≤ 1) :
    clusterLabelError PT hPT hm B (clusterKeptProductScope hPT M) ≤
      Real.exp (T.S.n k : ℝ) := by
  rw [clusterLabelError, if_pos hsmall]
  exact Real.exp_le_exp.mpr (clusterLabelErrorExponent_le_dimension
    hGeom B hgood hsmall hcons hscale)

theorem clusterKeptProduct_nonneg_of_data {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (W : ClusterHistory PT hPT hm) (I : ClusterInternalData PT)
    (i : Fin PT.tiling.m) (x : Fin (T.S.N k)) (M : ClusterMask PT) :
    0 ≤ clusterKeptProduct PT hPT hm i x M W I :=
  clusterKeptProduct_nonneg W I i x M

theorem clusterAfterLabelIntegral_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid}
    {hm : PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge}
    (CS : ClusterSample PT hPT hm) (i : Fin PT.tiling.m)
    (x : Fin (T.S.N k)) (M : ClusterMask PT) :
    0 ≤ clusterAfterLabelIntegral CS i x M := by
  classical
  unfold clusterAfterLabelIntegral FinLaw.E
  apply Finset.sum_nonneg
  intro W _
  apply mul_nonneg (CS.binStage.historyLaw.nonneg W)
  by_cases hload : clusterHistoryLoad PT hPT hm W
  · simp only [if_pos hload]
    apply Finset.sum_nonneg
    intro B _
    apply mul_nonneg ((CS.binStage.binLaw W).nonneg B)
    by_cases hmask : ClusterMaskConsistent PT hPT hm M B
    · simp only [if_pos hmask]
      apply Finset.sum_nonneg
      intro I _
      exact mul_nonneg ((clusterIndependentLabelKernel PT hPT hm W B).nonneg I)
        (clusterKeptProduct_nonneg W I i x M)
    · simp [hmask]
  · simp [hload]

theorem clusterHighMode_degree_window {κ : CConsts} (hκ : CConsts.Admissible κ)
    (T : Stage) :
    ∀ᶠ k in atTop, ∀ PT : ProfiledTiling κ T k, PT.Valid →
      (PT.tiling.mode = .highSmall ∨ PT.tiling.mode = .highLarge) → ∀ i,
        10 * Real.rpow ((PT.tiling.P i).q : ℝ) κ.Cb /
          (T.S.n k : ℝ) ≤ 1 / 6 := by
  let nR : ℕ → ℝ := fun k => (T.S.n k : ℝ)
  let logN : ℕ → ℝ := fun k => Real.log (nR k)
  have hn : Tendsto nR atTop atTop :=
    (tendsto_natCast_atTop_atTop).comp T.S.n_tendsto
  have ht : Tendsto logN atTop atTop := Real.tendsto_log_atTop.comp hn
  have hlogOne : ∀ᶠ k in atTop, 1 ≤ logN k :=
    ht.eventually (eventually_ge_atTop (1 : ℝ))
  let c : ℕ := Nat.ceil κ.Cb
  let m : ℕ := 2 * c
  have hratio : Tendsto (fun k => logN k ^ m / nR k) atTop (nhds 0) := by
    have htemp := (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 m one_ne_zero).comp hn
    change Tendsto (fun k => Real.log (nR k) ^ m / (1 * nR k + 0)) atTop (nhds 0) at htemp
    simpa only [one_mul, add_zero, logN] using htemp
  have hratioSmall : ∀ᶠ k in atTop, logN k ^ m / nR k < 1 / 60 :=
    hratio.eventually (Iio_mem_nhds (by norm_num))
  have hnLarge : ∀ᶠ k in atTop, 3600 ≤ nR k :=
    hn.eventually (eventually_ge_atTop (3600 : ℝ))
  filter_upwards [hlogOne, hratioSmall, hnLarge] with k ht1 hsmall hn3600
  intro PT hPT hm i
  let q : ℝ := (PT.tiling.P i).q
  let n : ℝ := nR k
  have hnPos : 0 < n := by linarith
  have hCb : 100 < κ.Cb := by
    have hratioAC : 0 < κ.aC / κ.aB := div_pos hκ.aC_rng.1 hκ.aB_rng.1
    have hEq : (100 : ℝ) * κ.aC / κ.aB = 100 * (κ.aC / κ.aB) := by ring
    have hCbBig := hκ.Cb_big
    rw [hEq] at hCbBig
    linarith
  have hCbPos : 0 < κ.Cb := by linarith [hCb]
  have hCbCeil : κ.Cb ≤ (c : ℝ) := by simpa [c] using (Nat.le_ceil κ.Cb)
  have hMhiPos : 0 < (κ.Mhi : ℝ) := by
    have hCbMlo : κ.Cb + 100 < (κ.Mlo : ℝ) := hκ.Mlo_big
    have hMloPos : 0 < (κ.Mlo : ℝ) := by linarith [hCb, hCbMlo]
    have hMhiLower : (κ.Mlo : ℝ) ≤ (κ.Mhi : ℝ) := by
      have hnonneg : 0 ≤ 10 / κ.cq := div_nonneg (by norm_num) hκ.cq_rng.1.le
      linarith [hκ.Mhi_big.1, hnonneg]
    exact lt_of_lt_of_le hMloPos hMhiLower
  have hMhiGtCb : κ.Cb < (κ.Mhi : ℝ) := by
    have hCbMlo : κ.Cb + 100 < (κ.Mlo : ℝ) := hκ.Mlo_big
    have hMhiLower : (κ.Mlo : ℝ) ≤ (κ.Mhi : ℝ) := by
      have hnonneg : 0 ≤ 10 / κ.cq := div_nonneg (by norm_num) hκ.cq_rng.1.le
      linarith [hκ.Mhi_big.1, hnonneg]
    exact lt_of_lt_of_le (by linarith) hMhiLower
  have hratioM : 0 < κ.Cb / (κ.Mhi : ℝ) ∧ κ.Cb / (κ.Mhi : ℝ) < 1 := by
    constructor
    · exact div_pos hCbPos hMhiPos
    · exact (div_lt_one hMhiPos).2 hMhiGtCb
  have hIotaSmall : κ.ι < 1 / 100000 := by
    have hmin₁ := min_le_right κ.xs (min κ.η0 (1 / 100 : ℝ))
    have hmin₂ := min_le_right κ.η0 (1 / 100 : ℝ)
    have hmin : min κ.xs (min κ.η0 (1 / 100 : ℝ)) ≤ 1 / 100 := le_trans hmin₁ hmin₂
    have hdiv : min κ.xs (min κ.η0 (1 / 100 : ℝ)) / 1000 ≤ 1 / 100000 := by
      calc
        _ ≤ (1 / 100 : ℝ) / 1000 := div_le_div_of_nonneg_right hmin (by norm_num)
        _ = 1 / 100000 := by norm_num
    have hIota := hκ.ι_rng.2
    norm_num at hIota
    exact hIota.trans_le hdiv
  have hθ : 0 ≤ κ.ι * κ.Cb / (κ.Mhi : ℝ) ∧
      κ.ι * κ.Cb / (κ.Mhi : ℝ) ≤ 1 / 2 := by
    have hmul := mul_lt_mul_of_pos_left hratioM.2 hκ.ι_rng.1
    have hident : κ.ι * κ.Cb / (κ.Mhi : ℝ) = κ.ι * (κ.Cb / (κ.Mhi : ℝ)) := by ring
    constructor
    · exact div_nonneg (mul_nonneg hκ.ι_rng.1.le hCbPos.le) hMhiPos.le
    · rw [hident]
      linarith
  rcases hm with hsmallMode | hlargeMode
  · have hdata := hPT.tiling_valid.cluster_data (Or.inr (Or.inl hsmallMode)) i
    rcases hdata with ⟨_, _, _, _, _, _, _, _, _, _, hsmallIff, _⟩
    have hsmallParts := hsmallIff.mp hsmallMode
    have hqOne : 1 ≤ q := by
      have hqlo : Real.rpow (logN k) κ.cq < q := by
        simpa [q, logN, nR] using hsmallParts.1
      have hpowOne : 1 ≤ Real.rpow (logN k) κ.cq := Real.one_le_rpow ht1 hκ.cq_rng.1.le
      exact le_trans hpowOne hqlo.le
    have hqUpper : q ≤ Real.rpow (logN k) 2 := by
      simpa [q, logN, nR, Real.rpow_natCast] using hsmallParts.2
    have hqCb : Real.rpow q κ.Cb ≤ (logN k) ^ m := by
      have hbase : 1 ≤ Real.rpow (logN k) 2 := by
        exact Real.one_le_rpow ht1 (by norm_num)
      have h1 : Real.rpow q κ.Cb ≤ Real.rpow (Real.rpow (logN k) 2) κ.Cb :=
        Real.rpow_le_rpow (by positivity) hqUpper hCbPos.le
      have h2 : Real.rpow (Real.rpow (logN k) 2) κ.Cb ≤
          Real.rpow (Real.rpow (logN k) 2) (c : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase hCbCeil
      have h3 : Real.rpow (Real.rpow (logN k) 2) (c : ℝ) =
          Real.rpow (logN k) (m : ℝ) := by
        calc
          _ = Real.rpow (logN k) (2 * (c : ℝ)) :=
            (Real.rpow_mul (by positivity : 0 ≤ logN k) 2 (c : ℝ)).symm
          _ = Real.rpow (logN k) (m : ℝ) := by simp [m, c, Nat.cast_mul]
      have h4 : Real.rpow (logN k) (m : ℝ) = (logN k) ^ m := Real.rpow_natCast _ _
      calc
        _ ≤ Real.rpow (Real.rpow (logN k) 2) κ.Cb := h1
        _ ≤ Real.rpow (Real.rpow (logN k) 2) (c : ℝ) := h2
        _ = Real.rpow (logN k) (m : ℝ) := h3
        _ = (logN k) ^ m := h4
    have hratioBound : Real.rpow q κ.Cb / n ≤ logN k ^ m / n :=
      div_le_div_of_nonneg_right hqCb (le_of_lt hnPos)
    exact le_of_lt (calc
      _ = 10 * (Real.rpow q κ.Cb / n) := by ring
      _ ≤ 10 * (logN k ^ m / n) := by gcongr
      _ < 10 * (1 / 60) := by nlinarith [hratioBound, hsmall]
      _ = 1 / 6 := by norm_num)
  · have hdata := hPT.tiling_valid.cluster_data (Or.inr (Or.inr hlargeMode)) i
    rcases hdata with ⟨_, _, _, _, _, _, _, hheightLower, _, _, _, hlargeIff⟩
    have hqSq : Real.log n ^ 2 < q := by
      have h := hlargeIff.mp hlargeMode
      simpa [q, n] using h
    have hqOne : 1 ≤ q := by
      have hlogSq : 1 ≤ Real.log n ^ 2 := by nlinarith [sq_nonneg (Real.log n - 1)]
      linarith
    have hheightLower' : Real.rpow q (κ.Mhi : ℝ) ≤ (PT.tiling.P i).h := by
      simpa [q, hlargeMode] using hheightLower
    have halloc := hPT.tiling_valid.allocation_bounds i
    have hheightUpper : ((PT.tiling.P i).h : ℝ) < n ^ κ.ι := by
      have hmax : (PT.tiling.P i).h ≤ max (PT.tiling.P i).h (PT.tiling.P i).ℓ :=
        Nat.le_max_left _ _
      have hmaxR : ((PT.tiling.P i).h : ℝ) ≤
          (max (PT.tiling.P i).h (PT.tiling.P i).ℓ : ℝ) := by exact_mod_cast hmax
      exact hmaxR.trans_lt (by simpa [n, nR] using halloc.1)
    have hpowN : Real.rpow q (κ.Mhi : ℝ) < Real.rpow n κ.ι :=
      lt_of_le_of_lt hheightLower' hheightUpper
    have hleft : Real.rpow (Real.rpow q (κ.Mhi : ℝ))
        (κ.Cb / (κ.Mhi : ℝ)) = Real.rpow q κ.Cb := by
      calc
        _ = Real.rpow q ((κ.Mhi : ℝ) * (κ.Cb / (κ.Mhi : ℝ))) :=
          (Real.rpow_mul (by positivity : 0 ≤ q) _ _).symm
        _ = Real.rpow q κ.Cb := by congr 1; field_simp [hMhiPos.ne']
    have hright : Real.rpow (Real.rpow n κ.ι) (κ.Cb / (κ.Mhi : ℝ)) =
        Real.rpow n (κ.ι * κ.Cb / (κ.Mhi : ℝ)) := by
      calc
        _ = Real.rpow n (κ.ι * (κ.Cb / (κ.Mhi : ℝ))) :=
          (Real.rpow_mul (by positivity : 0 ≤ n) _ _).symm
        _ = Real.rpow n (κ.ι * κ.Cb / (κ.Mhi : ℝ)) := by congr 1; ring
    have hraise := Real.rpow_le_rpow
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hqOne) _).le
      hpowN.le hratioM.1.le
    have hqCb : Real.rpow q κ.Cb ≤ Real.rpow n (κ.ι * κ.Cb / (κ.Mhi : ℝ)) := by
      calc
        _ = Real.rpow (Real.rpow q (κ.Mhi : ℝ)) (κ.Cb / (κ.Mhi : ℝ)) := hleft.symm
        _ ≤ Real.rpow (Real.rpow n κ.ι) (κ.Cb / (κ.Mhi : ℝ)) := hraise
        _ = Real.rpow n (κ.ι * κ.Cb / (κ.Mhi : ℝ)) := hright
    have hrootLe : Real.rpow n (κ.ι * κ.Cb / (κ.Mhi : ℝ)) ≤ Real.rpow n (1 / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hθ.2
    have hsquare : Real.sqrt n * Real.sqrt n = n := by
      nlinarith [Real.sq_sqrt (by linarith : 0 ≤ n)]
    have hsqrtRpow : Real.rpow n (1 / 2) = Real.sqrt n := (Real.sqrt_eq_rpow n).symm
    have hroot : 60 ≤ Real.sqrt n := by
      calc
        (60 : ℝ) = Real.sqrt 3600 := by norm_num
        _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hn3600
    have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnPos
    have hrootRatio : Real.sqrt n / n ≤ 1 / 60 := by
      have heq : Real.sqrt n / n = 1 / Real.sqrt n := by
        calc
          _ = Real.sqrt n / (Real.sqrt n * Real.sqrt n) :=
            congrArg (fun d : ℝ => Real.sqrt n / d) hsquare.symm
          _ = 1 / Real.sqrt n := by field_simp [hsqrtPos.ne']
      rw [heq]
      exact one_div_le_one_div_of_le (by norm_num) hroot
    have hratioBound : Real.rpow q κ.Cb / n ≤ 1 / 60 := by
      calc
        _ ≤ Real.rpow n (κ.ι * κ.Cb / (κ.Mhi : ℝ)) / n :=
          div_le_div_of_nonneg_right hqCb (le_of_lt hnPos)
        _ ≤ Real.rpow n (1 / 2) / n :=
          div_le_div_of_nonneg_right hrootLe (le_of_lt hnPos)
        _ = Real.sqrt n / n := by rw [hsqrtRpow]
        _ ≤ 1 / 60 := hrootRatio
    calc
      _ = 10 * (Real.rpow q κ.Cb / n) := by ring
      _ ≤ 10 * (1 / 60) := by gcongr
      _ = 1 / 6 := by norm_num

theorem two_exp_le_exp_two_pow {n : ℕ} (hn : 1 ≤ n) :
    2 * Real.exp (n : ℝ) ≤ (Real.exp 2) ^ n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2exp : 2 ≤ Real.exp (n : ℝ) := by
    have h := Real.add_one_le_exp (n : ℝ)
    nlinarith
  calc
    2 * Real.exp (n : ℝ) ≤ Real.exp (n : ℝ) * Real.exp (n : ℝ) :=
      mul_le_mul_of_nonneg_right h2exp (le_of_lt (Real.exp_pos _))
    _ = Real.exp ((n : ℝ) * 2) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ = (Real.exp 2) ^ n := by
      rw [mul_comm (n : ℝ) 2, ← Real.exp_nat_mul]
      congr 1
      ring

end HypercubeRamsey.Lane_q_s15_c2
