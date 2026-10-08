import HypercubeRamsey.S13.Allocation_q_s13_alloc
import Mathlib.Data.List.Induction

namespace HypercubeRamsey.Lane_sol_s13_allocB

open scoped BigOperators
open Classical

private theorem leaf_card {n ell : ℕ} (w : CubePos n) (hell : ell ≤ n) :
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} = 2 ^ (n - ell) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter fun j => j.val < ell
  let e : Fin ell ↪ Fin n := {
    toFun := fun j => ⟨j.val, j.isLt.trans_le hell⟩
    inj' := by
      intro a b hab
      have hv := congrArg (fun x : Fin n => x.val) hab
      change a.val = b.val at hv
      exact Fin.ext hv
  }
  have hS_eq : S = Finset.univ.map e := by
    ext j
    constructor
    · intro hj
      have hj' := (Finset.mem_filter.mp hj).2
      refine Finset.mem_map.mpr ⟨⟨j.val, hj'⟩, Finset.mem_univ _, ?_⟩
      exact Fin.ext rfl
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨j', hj', hEq⟩
      subst j
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j'.isLt⟩
  have hScard : S.card = ell := by
    rw [hS_eq]
    simp
  let choices : Fin n → Finset Bool := fun j =>
    if j ∈ S then {w j} else Finset.univ
  let Q := Fintype.piFinset choices
  have hpred (v : CubePos n) : v ∈ prefixLeaf ell w ↔ v ∈ Q := by
    change (∀ j : Fin n, j.val < ell → v j = w j) ↔ v ∈ Q
    constructor
    · intro hv
      apply Fintype.mem_piFinset.mpr
      intro j
      by_cases hj : j ∈ S
      · have hfix := hv j (Finset.mem_filter.mp hj).2
        simp [Q, choices, hj, hfix]
      · simp [Q, choices, hj]
    · intro hv j hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      have hmem := Fintype.mem_piFinset.mp hv j
      simpa [Q, choices, hjS] using hmem
  have hF : Finset.univ.filter (fun v : CubePos n => v ∈ prefixLeaf ell w) = Q := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpred v
  have hsub := Fintype.card_congr ((Equiv.refl (CubePos n)).subtypeEquiv hpred)
  calc
    Fintype.card {v : CubePos n // v ∈ prefixLeaf ell w} =
        Fintype.card {v : CubePos n // v ∈ Q} := hsub
    _ = Q.card := Fintype.card_coe Q
    _ = 2 ^ (n - ell) := by
      change (Fintype.piFinset choices).card = _
      rw [Fintype.card_piFinset]
      have hchoice : ∀ j : Fin n, (choices j).card = if j ∈ S then 1 else 2 := by
        intro j
        by_cases hj : j ∈ S <;> simp [choices, hj]
      simp_rw [hchoice]
      rw [Finset.prod_ite]
      have hfilter : Finset.univ.filter (fun j : Fin n => j ∉ S) = Finset.univ \ S := by
        ext j
        simp
      rw [hfilter, Finset.prod_const_one, Finset.prod_const (b := 2),
        Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp [hScard]

private noncomputable def leafSet {n : ℕ} (ell : ℕ) (w : CubePos n) : Finset (CubePos n) :=
  Finset.univ.filter fun v => v ∈ prefixLeaf ell w

private theorem mem_leafSet {n ell : ℕ} (w v : CubePos n) :
    v ∈ leafSet ell w ↔ v ∈ prefixLeaf ell w := by
  simp [leafSet]

private theorem leafSet_card {n ell : ℕ} (w : CubePos n) (hell : ell ≤ n) :
    (leafSet ell w).card = 2 ^ (n - ell) := by
  simpa [leafSet] using leaf_card w hell

private theorem leaf_disjoint {n a b : ℕ} (u v : CubePos n) (hab : a ≤ b)
    (hv : v ∉ prefixLeaf a u) : Disjoint (leafSet a u) (leafSet b v) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  apply hv
  have hx' := (mem_leafSet u x).mp hx
  have hy' := (mem_leafSet v x).mp hy
  intro j hj
  exact (hy' j (hj.trans_le hab)).symm.trans (hx' j hj)

/-- Greedily place prefixes in order of increasing length. -/
private theorem pack_list {α : Type*} [DecidableEq α] (n : ℕ) (ell : α → ℕ)
    (l : List α) (hnodup : l.Nodup)
    (hsorted : l.Pairwise fun i j => ell i ≤ ell j)
    (hlength : ∀ i ∈ l, ell i ≤ n)
    (hmass : (l.map fun i => 2 ^ (n - ell i)).sum ≤ 2 ^ n) :
    ∃ w : α → CubePos n, ∀ i ∈ l, ∀ j ∈ l, i ≠ j →
      Disjoint (leafSet (ell i) (w i)) (leafSet (ell j) (w j)) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨fun _ _ => false, by simp⟩
  | append_singleton l a ih =>
    have hn := List.nodup_append.mp hnodup
    have hs := List.pairwise_append.mp hsorted
    have haNot : a ∉ l := by
      intro ha
      exact hn.2.2 a ha a (by simp) rfl
    have hsum : (l.map fun i => 2 ^ (n - ell i)).sum + 2 ^ (n - ell a) ≤ 2 ^ n := by
      simpa using hmass
    have hsumLt : (l.map fun i => 2 ^ (n - ell i)).sum < 2 ^ n := by
      have hp : 0 < 2 ^ (n - ell a) := by positivity
      omega
    obtain ⟨w, hw⟩ := ih hn.1 hs.1 (fun i hi => hlength i (by simp [hi])) hsumLt.le
    let U := l.toFinset.biUnion fun i => leafSet (ell i) (w i)
    have hU : U.card < (Finset.univ : Finset (CubePos n)).card := by
      calc
        U.card ≤ ∑ i ∈ l.toFinset, (leafSet (ell i) (w i)).card := Finset.card_biUnion_le
        _ = ∑ i ∈ l.toFinset, 2 ^ (n - ell i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact leafSet_card (w i) (hlength i (by simp [List.mem_toFinset.mp hi]))
        _ = (l.map fun i => 2 ^ (n - ell i)).sum :=
          S13.allocation_list_sum_toFinset _ l hn.1
        _ < 2 ^ n := hsumLt
        _ = (Finset.univ : Finset (CubePos n)).card := by simp [CubePos]
    obtain ⟨v, _, hv⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
    have hvOld (i : α) (hi : i ∈ l) : v ∉ prefixLeaf (ell i) (w i) := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr ⟨i, by simpa using hi, (mem_leafSet _ _).mpr h⟩
    let w' := Function.update w a v
    have hold (i : α) (hi : i ∈ l) : w' i = w i := by
      apply Function.update_of_ne
      intro h
      exact haNot (h ▸ hi)
    have hnew : w' a = v := Function.update_self _ _ _
    have hdisj (i : α) (hi : i ∈ l) :
        Disjoint (leafSet (ell i) (w' i)) (leafSet (ell a) (w' a)) := by
      rw [hold i hi, hnew]
      exact leaf_disjoint (w i) v (hs.2.2 i hi a (by simp)) (hvOld i hi)
    refine ⟨w', ?_⟩
    intro i hi j hj hij
    rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hj with hj | hj
      · rw [hold i hi, hold j hj]
        exact hw i hi j hj hij
      · have heq : j = a := by simpa using hj
        subst j
        exact hdisj i hi
    · have heq : i = a := by simpa using hi
      subst i
      rcases List.mem_append.mp hj with hj | hj
      · exact (hdisj j hj).symm
      · have heq : j = a := by simpa using hj
        exact (hij heq.symm).elim

/-- Dyadic equality fills the cube with disjoint initial-coordinate leaves. -/
theorem complete_prefix {m n : ℕ} (ell : Fin m → ℕ) (hlength : ∀ i, ell i ≤ n)
    (hmass : ∑ i, 2 ^ (n - ell i) = 2 ^ n) :
    ∃ w : Fin m → CubePos n, ∀ v : CubePos n, ∃! i, v ∈ prefixLeaf (ell i) (w i) := by
  let rel : Fin m → Fin m → Prop := fun i j => ell i ≤ ell j
  let order := List.insertionSort rel (List.finRange m)
  have hperm : order.Perm (List.finRange m) := List.perm_insertionSort rel _
  have hnodup : order.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange _)
  have hmem (i : Fin m) : i ∈ order := hperm.mem_iff.mpr (by simp)
  have hsum : (order.map fun i => 2 ^ (n - ell i)).sum = 2 ^ n := by
    rw [(hperm.map _).sum_eq, ← Fin.sum_univ_def]
    exact hmass
  obtain ⟨w, hw⟩ := pack_list n ell order hnodup (List.pairwise_insertionSort rel _)
    (fun i _ => hlength i) hsum.le
  have hdisj : (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => leafSet (ell i) (w i)) := by
    intro i _ j _ hij
    exact hw i (hmem i) j (hmem j) hij
  let U := Finset.univ.biUnion fun i => leafSet (ell i) (w i)
  have hU : U = Finset.univ := by
    apply Finset.eq_univ_of_card
    calc
      U.card = ∑ i, (leafSet (ell i) (w i)).card := Finset.card_biUnion hdisj
      _ = ∑ i, 2 ^ (n - ell i) := Finset.sum_congr rfl (fun i _ => leafSet_card _ (hlength i))
      _ = 2 ^ n := hmass
      _ = Fintype.card (CubePos n) := by simp [CubePos]
  refine ⟨w, ?_⟩
  intro v
  have hv : v ∈ U := by rw [hU]; simp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  refine ⟨i, (mem_leafSet _ _).mp hi, ?_⟩
  intro j hj
  by_contra hne
  exact Finset.disjoint_left.mp (hw j (hmem j) i (hmem i) hne)
    ((mem_leafSet _ _).mpr hj) hi

/-- Convert the reciprocal-power Kraft equality to the finite cube volume equality. -/
theorem complete_prefix_of_kraft {m n : ℕ} (ell : Fin m → ℕ) (hlength : ∀ i, ell i ≤ n)
    (hmass : ∑ i, (2 : ℝ) ^ (-(ell i : ℤ)) = 1) :
    ∃ w : Fin m → CubePos n, ∀ v : CubePos n, ∃! i, v ∈ prefixLeaf (ell i) (w i) := by
  have hterm (i : Fin m) : (2 : ℝ) ^ n * (2 : ℝ) ^ (-(ell i : ℤ)) =
      (2 : ℝ) ^ (n - ell i) := by
    have he : (n : ℤ) + -(ell i : ℤ) = ((n - ell i : ℕ) : ℤ) := by
      have hi := hlength i
      omega
    calc
      _ = (2 : ℝ) ^ ((n : ℤ) + -(ell i : ℤ)) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
      _ = (2 : ℝ) ^ (n - ell i) := by rw [he, zpow_natCast]
  have hvol : ∑ i, (2 : ℝ) ^ (n - ell i) = (2 : ℝ) ^ n := by
    calc
      _ = ∑ i, (2 : ℝ) ^ n * (2 : ℝ) ^ (-(ell i : ℤ)) :=
        Finset.sum_congr rfl (fun i _ => (hterm i).symm)
      _ = (2 : ℝ) ^ n * (∑ i, (2 : ℝ) ^ (-(ell i : ℤ))) := by rw [Finset.mul_sum]
      _ = (2 : ℝ) ^ n := by rw [hmass, mul_one]
  apply complete_prefix ell hlength
  exact_mod_cast hvol

end HypercubeRamsey.Lane_sol_s13_allocB
