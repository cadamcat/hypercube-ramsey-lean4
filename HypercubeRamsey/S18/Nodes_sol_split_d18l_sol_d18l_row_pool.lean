import HypercubeRamsey.S17.Defs
import HypercubeRamsey.S16.Geometry_sol_s16_poolcmp
import HypercubeRamsey.S16.Comparisons_q_s16_comp1
import HypercubeRamsey.S16.Comparisons_q_s16_comp2

namespace HypercubeRamsey.S18.Lane_sol_d18l_row

open Classical
open S16
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

namespace PC
open HypercubeRamsey.Lane_sol_s16_poolcmp

abbrev CellSlot (G : LowGeom PT) := Σ C : G.Cell, Fin (G.nslot C)
abbrev PoolAssignment (G : LowGeom PT) := ∀ C, CellPool G C

def DependsOnCellSlots {G : LowGeom PT} (S : Finset (CellSlot G))
    (f : PoolAssignment G → ℝ) : Prop :=
  ∀ P Q, (∀ s ∈ S, P s.1 s.2 = Q s.1 s.2) → f P = f Q

private theorem pr_indicator {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = P.E (fun x => if A x then 1 else 0) := by
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : A x <;> simp [hx]

private theorem map_pr {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (P : FinLaw Ω) (f : Ω → Ξ) (A : Ξ → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun x => A (f x)) := by
  rw [pr_indicator, pr_indicator]
  exact map_E P f (fun x => if A x then 1 else 0)

private theorem pr_compl {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr (fun x => ¬ A x) = 1 - P.pr A := by
  have hsum : P.pr A + P.pr (fun x => ¬ A x) = 1 := by
    unfold FinLaw.pr
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ x, P.w x := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : A x <;> simp [hx]
      _ = 1 := P.sum_one
  linarith

abbrev Query (G : LowGeom PT) (S : Finset (CellSlot G)) (i : Fin PT.tiling.m) :=
  {s : CellSlot G // s ∈ S ∧ G.cellPatch s.1 = i}

abbrev Readout (G : LowGeom PT) (S : Finset (CellSlot G)) :=
  ∀ i : Fin PT.tiling.m, Query G S i → Bin PT.tiling i

noncomputable def readout (G : LowGeom PT) (S : Finset (CellSlot G))
    (P : PoolAssignment G) : Readout G S := fun i s =>
  ⟨(P s.1.1 s.1.2).1, by
    have aux {j : Fin PT.tiling.m} (h : j = i) (B : Bin PT.tiling j) :
        B.1 ∈ (PT.tiling.P i).bins.parts := by
      cases h
      exact B.2
    exact aux s.2.2 (P s.1.1 s.1.2)⟩

noncomputable def valid (G : LowGeom PT) (S : Finset (CellSlot G)) : Finset (Readout G S) :=
  Finset.univ.filter fun a => ∀ i, Function.Injective (a i)

theorem readout_injective (G : LowGeom PT) (S : Finset (CellSlot G))
    (P : PoolAssignment G) (hP : P ∈ permPools G) : ∀ i, Function.Injective (readout G S P i) := by
  intro i s t hst
  have h := (Finset.mem_filter.mp hP).2 s.1.1 t.1.1 s.1.2 t.1.2
    (s.2.2.trans t.2.2.symm) (congrArg Subtype.val hst)
  apply Subtype.ext
  rcases s with ⟨⟨C, a⟩, hs⟩
  rcases t with ⟨⟨D, b⟩, ht⟩
  rcases h with ⟨hCD, hab⟩
  change C = D at hCD
  subst D
  change a.val = b.val at hab
  have hslots : a = b := Fin.ext hab
  subst b
  rfl

private theorem bin_transport_apply (e : ∀ i : Fin PT.tiling.m, Equiv.Perm (Bin PT.tiling i))
    (i j : Fin PT.tiling.m) (h : i = j) (B : Bin PT.tiling i) :
    binEquiv h (e i B) = e j (binEquiv h B) := by
  subst j
  rfl

theorem readout_relabel (G : LowGeom PT) (S : Finset (CellSlot G))
    (e : ∀ i : Fin PT.tiling.m, Equiv.Perm (Bin PT.tiling i)) (P : PoolAssignment G) :
    readout G S (relabel G e P) = fun i s => e i (readout G S P i s) := by
  funext i s
  exact bin_transport_apply e _ i s.2.2 (P s.1.1 s.1.2)

/-- The complete queried permutation marginal is uniform on assignments
injective within each patch, even when the queried scope spans patches. -/
theorem perm_query (G : LowGeom PT) (hpools : (permPools G).Nonempty)
    (S : Finset (CellSlot G)) :
    ∃ hU : (valid G S).Nonempty,
      FinLaw.map (permPoolLaw G hpools) (readout G S) = FinLaw.uniform (valid G S) hU := by
  have hU : (valid G S).Nonempty := ⟨readout G S hpools.choose,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, readout_injective G S _ hpools.choose_spec⟩⟩
  refine ⟨hU, map_uniform_of_symmetry _ _ _ hU ?_ ?_⟩
  · intro P hP
    have hmem : P ∈ permPools G := by
      by_contra hn
      exact hP (by simp [permPoolLaw, FinLaw.uniform, hn])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, readout_injective G S P hmem⟩
  · intro x hx y hy
    have hext (i : Fin PT.tiling.m) :
        ∃ e : Equiv.Perm (Bin PT.tiling i), ∀ s, e (x i s) = y i s :=
      Equiv.Perm.exists_extending_pair (x i) (y i)
        ((Finset.mem_filter.mp hx).2 i) ((Finset.mem_filter.mp hy).2 i)
    let e i := Classical.choose (hext i)
    have he i := Classical.choose_spec (hext i)
    refine ⟨relabel G e, perm_weight_relabel G hpools e, ?_⟩
    intro P
    rw [readout_relabel]
    constructor
    · intro h
      funext i s
      apply (e i).injective
      exact (congrFun (congrFun h i) s).trans (he i s).symm
    · intro h
      funext i s
      rw [h]
      exact he i s

noncomputable def slotPerm (G : LowGeom PT) (S : Finset (CellSlot G))
    (x y : Readout G S) (C : G.Cell) (j : Fin (G.nslot C)) :
    Equiv.Perm (Bin PT.tiling (G.cellPatch C)) :=
  if hs : (⟨C, j⟩ : CellSlot G) ∈ S then
    Equiv.swap (x _ ⟨⟨C, j⟩, hs, rfl⟩) (y _ ⟨⟨C, j⟩, hs, rfl⟩)
  else Equiv.refl _

/-- The complete queried iid marginal is uniform on every assignment. -/
theorem iid_query (G : LowGeom PT) (hpools : (permPools G).Nonempty)
    (S : Finset (CellSlot G)) :
    FinLaw.map (iidPoolLaw G hpools) (readout G S) =
      FinLaw.uniform Finset.univ ⟨readout G S hpools.choose, Finset.mem_univ _⟩ := by
  apply map_uniform_of_symmetry
  · intro _ _
    exact Finset.mem_univ _
  · intro x _ y _
    refine ⟨relabelSlots G (slotPerm G S x y), ?_, ?_⟩
    · intro P
      simp [iidPoolLaw, FinLaw.uniform]
    · intro P
      constructor
      · intro h
        funext i s
        rcases s with ⟨⟨C, j⟩, hs, hi⟩
        subst i
        have hpoint := congrFun (congrFun h (G.cellPatch C)) ⟨⟨C, j⟩, hs, rfl⟩
        change (slotPerm G S x y C j) (P C j) =
          y (G.cellPatch C) ⟨⟨C, j⟩, hs, rfl⟩ at hpoint
        simp only [slotPerm, dite_eq_left hs] at hpoint
        apply (Equiv.swap (x _ ⟨⟨C, j⟩, hs, rfl⟩) (y _ ⟨⟨C, j⟩, hs, rfl⟩)).injective
        exact hpoint.trans (Equiv.swap_apply_left _ _).symm
      · intro h
        funext i s
        rcases s with ⟨⟨C, j⟩, hs, hi⟩
        subst i
        change (slotPerm G S x y C j) (P C j) =
          y (G.cellPatch C) ⟨⟨C, j⟩, hs, rfl⟩
        simp only [slotPerm, dite_eq_left hs]
        have hPx : P C j = x (G.cellPatch C) ⟨⟨C, j⟩, hs, rfl⟩ :=
          congrFun (congrFun h (G.cellPatch C)) ⟨⟨C, j⟩, hs, rfl⟩
        rw [hPx]
        exact Equiv.swap_apply_left _ _

/-- Small iid collision probability pays for the full queried permutation
comparison. No unqueried slot is restricted. -/
theorem scope_compare (G : LowGeom PT) (hpools : (permPools G).Nonempty)
    (S : Finset (CellSlot G)) (ε : ℝ) (hε : 0 ≤ ε)
    (hcollision : (iidPoolLaw G hpools).pr (fun P => readout G S P ∉ valid G S) ≤ ε / (1 + ε))
    (F : PoolAssignment G → ℝ) (hF : ∀ P, 0 ≤ F P)
    (hl : DependsOnCellSlots S F) :
    (permPoolLaw G hpools).E F ≤ (1 + ε) * (iidPoolLaw G hpools).E F := by
  obtain ⟨f, hf, hfactor⟩ := factor_test (readout G S) F hF (by
    intro P Q hread
    apply hl P Q
    intro s hs
    have hpoint := congrFun (congrFun hread (G.cellPatch s.1)) ⟨s, hs, rfl⟩
    exact Subtype.ext (congrArg Subtype.val hpoint))
  have hFdef : F = fun P => f (readout G S P) := funext hfactor
  obtain ⟨hU, hperm⟩ := perm_query G hpools S
  have hiid := iid_query G hpools S
  let U := valid G S
  let V := (Finset.univ : Finset (Readout G S))
  have hUc : 0 < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU
  have hVc : 0 < (V.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨readout G S hpools.choose, Finset.mem_univ _⟩
  have hmass : (U.card : ℝ) / V.card ≥ 1 / (1 + ε) := by
    have hp := map_pr (iidPoolLaw G hpools) (readout G S)
      (fun a => a ∉ U)
    rw [hiid] at hp
    have hcompl : (FinLaw.uniform V ⟨readout G S hpools.choose, Finset.mem_univ _⟩).pr
        (fun a => a ∉ U) = 1 - (U.card : ℝ) / V.card := by
      rw [pr_compl]
      simp [FinLaw.pr, FinLaw.uniform, V, Finset.sum_ite_mem, ← Finset.mul_sum,
        div_eq_mul_inv]
    rw [hcompl] at hp
    rw [← hp] at hcollision
    have hden : 0 < 1 + ε := by positivity
    have hsum : 1 - ε / (1 + ε) = 1 / (1 + ε) := by field_simp; ring
    linarith
  have hcoef : 1 / (U.card : ℝ) ≤ (1 + ε) / V.card := by
    have hden : 0 < 1 + ε := by positivity
    have h := (div_le_div_iff₀ hden hVc).mp hmass
    exact (div_le_div_iff₀ hUc hVc).mpr (by nlinarith)
  have hsum : (∑ a ∈ U, f a) ≤ ∑ a, f a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hf a)
  have hsum0 : 0 ≤ ∑ a, f a := Finset.sum_nonneg (fun a _ => hf a)
  rw [hFdef, ← map_E (permPoolLaw G hpools) (readout G S) f,
    ← map_E (iidPoolLaw G hpools) (readout G S) f, hperm, hiid]
  have hEU : (FinLaw.uniform U hU).E f = (∑ a ∈ U, f a) / U.card := by
    simp only [FinLaw.E, FinLaw.uniform, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
    ring
  have hEV : (FinLaw.uniform V ⟨readout G S hpools.choose, Finset.mem_univ _⟩).E f =
      (∑ a, f a) / V.card := by
    simp only [FinLaw.E, FinLaw.uniform, V, Finset.mem_univ, if_true, ← Finset.mul_sum]
    ring
  rw [hEU, hEV]
  apply (div_le_div_of_nonneg_right hsum hUc.le).trans
  have h := mul_le_mul_of_nonneg_right hcoef hsum0
  convert h using 1 <;> ring

/-- Any pair of distinct queried slots in the same patch has the usual
uniform iid collision probability. -/
theorem pair_collision (G : LowGeom PT) (hpools : (permPools G).Nonempty)
    (s t : CellSlot G) (hne : s ≠ t) (hp : G.cellPatch t.1 = G.cellPatch s.1) :
    (iidPoolLaw G hpools).pr (fun P => (P s.1 s.2).1 = (P t.1 t.2).1) =
      1 / (Fintype.card (Bin PT.tiling (G.cellPatch s.1)) : ℝ) := by
  let i := G.cellPatch s.1
  let A : Finset (CellSlot G) := {s, t}
  have hpatch : ∀ a ∈ A, G.cellPatch a.1 = i := by
    intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · subst a; rfl
    · rw [Finset.mem_singleton.mp ha]
      exact hp
  let R := restrict G i A hpatch
  let a : A := ⟨s, by simp [A]⟩
  let b : A := ⟨t, by simp [A]⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  let hBin : (Finset.univ : Finset (Bin PT.tiling i)).Nonempty :=
    ⟨R hpools.choose a, Finset.mem_univ _⟩
  let U : FinLaw (Bin PT.tiling i) := FinLaw.uniform Finset.univ hBin
  have hBc : 0 < (Fintype.card (Bin PT.tiling i) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨hBin.choose⟩
  have hproduct : FinLaw.uniform Finset.univ ⟨R hpools.choose, Finset.mem_univ _⟩ =
      FinLaw.pi (fun _ : A => U) := by
    apply Lane_q_s16_comp2.finLaw_ext
    intro f
    simp [FinLaw.uniform, FinLaw.pi, U, Fintype.card_fun, Nat.cast_pow,
      Finset.prod_const, div_pow]
  have hm := iid_marginal G hpools i A hpatch
  have hmap := map_pr (iidPoolLaw G hpools) R
    (fun x => x a = x b)
  rw [hm, hproduct] at hmap
  have hpred : (fun P => R P a = R P b) =
      (fun P => (P s.1 s.2).1 = (P t.1 t.2).1) := by
    funext P
    exact propext Subtype.ext_iff
  rw [hpred] at hmap
  rw [← hmap]
  exact HypercubeRamsey.Lane_q_s16_comp1.pi_pair_collision_uniform
    (fun _ : A => U) hBc (by intro _ B; simp [U, FinLaw.uniform]) a b hab

/-- A union over queried pairs avoids any factor for the number of patches. -/
theorem query_collision_bound (G : LowGeom PT) (hpools : (permPools G).Nonempty)
    (S : Finset (CellSlot G)) (B : ℝ) (hB : 0 < B)
    (hbins : ∀ i, B ≤ (Fintype.card (Bin PT.tiling i) : ℝ)) :
    (iidPoolLaw G hpools).pr (fun P => readout G S P ∉ valid G S) ≤
      (S.card : ℝ) ^ 2 / B := by
  let bad (q : S × S) (P : PoolAssignment G) :=
    q.1.1 ≠ q.2.1 ∧ G.cellPatch q.1.1.1 = G.cellPatch q.2.1.1 ∧
      (P q.1.1.1 q.1.1.2).1 = (P q.2.1.1 q.2.1.2).1
  have hcover (P : PoolAssignment G) (hn : readout G S P ∉ valid G S) :
      ∃ q : S × S, bad q P := by
    have hn' : ¬ ∀ i, Function.Injective (readout G S P i) := by simpa [valid] using hn
    obtain ⟨i, hi⟩ := not_forall.mp hn'
    obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hi
    let a' : S := ⟨a.1, a.2.1⟩
    let b' : S := ⟨b.1, b.2.1⟩
    refine ⟨(a', b'), ?_, a.2.2.trans b.2.2.symm, congrArg Subtype.val hab⟩
    intro h
    exact hne (Subtype.ext h)
  have hpair (q : S × S) : (iidPoolLaw G hpools).pr (bad q) ≤ 1 / B := by
    by_cases hn : q.1.1 = q.2.1
    · have hsubeq : q.1 = q.2 := Subtype.ext hn
      have hz : (iidPoolLaw G hpools).pr (bad q) = 0 := by simp [bad, hn, hsubeq, FinLaw.pr]
      rw [hz]
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB.le
    by_cases hp : G.cellPatch q.1.1.1 = G.cellPatch q.2.1.1
    · have hpred : bad q = (fun P => (P q.1.1.1 q.1.1.2).1 = (P q.2.1.1 q.2.1.2).1) := by
        funext P
        have hsub : q.1 ≠ q.2 := fun h => hn (congrArg Subtype.val h)
        simp [bad, hn, hp, hsub]
      rw [hpred, pair_collision G hpools _ _ hn hp.symm]
      exact one_div_le_one_div_of_le hB (hbins _)
    · have hz : (iidPoolLaw G hpools).pr (bad q) = 0 := by simp [bad, hp, FinLaw.pr]
      rw [hz]
      exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1) hB.le
  apply (Lane_q_s16_comp2.pr_mono _ _ _ hcover).trans
  apply (Lane_q_s16_comp2.pr_exists_le_sum _ bad).trans
  calc
    (∑ q : S × S, (iidPoolLaw G hpools).pr (bad q)) ≤ ∑ _q : S × S, 1 / B :=
      Finset.sum_le_sum (fun q _ => hpair q)
    _ = (S.card : ℝ) ^ 2 / B := by
      simp [Fintype.card_prod, Fintype.card_coe, Nat.cast_mul, pow_two]
      ring

/-- An explicit bin-cardinality budget implies the global scope comparison. -/
theorem scope_compare_of_bin_budget (G : LowGeom PT) (hpools : (permPools G).Nonempty)
    (S : Finset (CellSlot G)) (ε : ℝ) (hε : 0 < ε)
    (hbins : ∀ i, ((S.card : ℝ) ^ 2 * (1 + ε) / ε) ≤
      (Fintype.card (Bin PT.tiling i) : ℝ))
    (F : PoolAssignment G → ℝ) (hF : ∀ P, 0 ≤ F P) (hl : DependsOnCellSlots S F) :
    (permPoolLaw G hpools).E F ≤ (1 + ε) * (iidPoolLaw G hpools).E F := by
  by_cases hS : S.card = 0
  · have hlocal (P Q : PoolAssignment G) : F P = F Q := by
      apply hl P Q
      have hs : S = ∅ := Finset.card_eq_zero.mp hS
      simp [hs]
    have hFconst : F = fun _ => F hpools.choose := funext (fun P => hlocal P _)
    rw [hFconst]
    simp only [FinLaw.E, ← Finset.sum_mul, FinLaw.sum_one, one_mul]
    nlinarith [hF hpools.choose]
  · let B := (S.card : ℝ) ^ 2 * (1 + ε) / ε
    have hB : 0 < B := by
      have hSc : 0 < (S.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hS
      dsimp [B]
      positivity
    apply scope_compare G hpools S ε hε.le _ F hF hl
    have hcollision := query_collision_bound G hpools S B hB hbins
    apply hcollision.trans
    have hSne : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS
    dsimp [B]
    field_simp
    <;> nlinarith

/-- A single scalar budget supplies the S17 comparison for both permutation
pools and a positive global pin, with arbitrary queried patch scopes. -/
theorem pool_iid_comparison_of_budget (D : ListGateContext κ T k PT)
    (hpools : (permPools D.G).Nonempty) (q : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hbins : ∀ i, ((q + 1 : ℕ) : ℝ) ^ 2 * (1 + ε) / ε ≤
      (Fintype.card (Bin PT.tiling i) : ℝ))
    (μ : FinLaw D.PoolAssignment) (hμ : D.IsPermOrPinnedPoolLaw hpools μ) :
    ∃ ν : FinLaw D.PoolAssignment,
      (ν = iidPoolLaw D.G hpools ∨
        ∃ (pin : D.PoolPin) (hpin : 0 < ∑ pools ∈ D.poolPinSet pin,
          (iidPoolLaw D.G hpools).w pools),
          ν = FinLaw.cond (iidPoolLaw D.G hpools) (D.poolPinSet pin) hpin) ∧
      ∀ (slots : Finset (Σ C : D.G.Cell, Fin (D.G.nslot C)))
        (f : D.PoolAssignment → ℝ),
        slots.card ≤ q → (∀ pools, 0 ≤ f pools) →
        (∀ p r, (∀ a ∈ slots, p a.1 a.2 = r a.1 a.2) → f p = f r) →
        μ.E f ≤ (1 + ε) * ν.E f := by
  have hglobal (S : Finset (CellSlot D.G)) (hs : S.card ≤ q + 1)
      (f : D.PoolAssignment → ℝ) (hf : ∀ P, 0 ≤ f P)
      (hl : DependsOnCellSlots S f) :
      (permPoolLaw D.G hpools).E f ≤ (1 + ε) * (iidPoolLaw D.G hpools).E f := by
    apply scope_compare_of_bin_budget D.G hpools S ε hε _ f hf hl
    intro i
    apply le_trans _ (hbins i)
    apply div_le_div_of_nonneg_right _ hε.le
    apply mul_le_mul_of_nonneg_right _ (show 0 ≤ 1 + ε by positivity)
    have hsc : (S.card : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast hs
    have hsc0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg S.card
    nlinarith
  rcases hμ with rfl | ⟨pin, hpin, rfl⟩
  · exact ⟨iidPoolLaw D.G hpools, Or.inl rfl, fun S f hs hf hl =>
      hglobal S (hs.trans (Nat.le_succ _)) f hf hl⟩
  · have hmass := pin_mass_equal D.G hpools pin.cell pin.slot pin.bin
    change (∑ P ∈ D.poolPinSet pin, (permPoolLaw D.G hpools).w P) =
      ∑ P ∈ D.poolPinSet pin, (iidPoolLaw D.G hpools).w P at hmass
    have hid : 0 < ∑ P ∈ D.poolPinSet pin, (iidPoolLaw D.G hpools).w P := by
      rwa [← hmass]
    refine ⟨FinLaw.cond (iidPoolLaw D.G hpools) (D.poolPinSet pin) hid,
      Or.inr ⟨pin, hid, rfl⟩, ?_⟩
    intro S f hs hf hl
    let slot : CellSlot D.G := ⟨pin.cell, pin.slot⟩
    let test (P : D.PoolAssignment) := if P ∈ D.poolPinSet pin then f P else 0
    have hnonneg : ∀ P, 0 ≤ test P := by
      intro P
      dsimp [test]
      split_ifs <;> simp_all
    have hlocal : DependsOnCellSlots (insert slot S) test := by
      intro P Q hPQ
      have heq := hPQ slot (Finset.mem_insert_self _ _)
      have hpinEq : (P ∈ D.poolPinSet pin) ↔ (Q ∈ D.poolPinSet pin) := by
        simp only [ListGateContext.poolPinSet, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show P pin.cell pin.slot = Q pin.cell pin.slot from heq]
      dsimp [test]
      by_cases hp : P ∈ D.poolPinSet pin
      · have hq := hpinEq.mp hp
        simp only [if_pos hp, if_pos hq]
        exact hl P Q (fun a ha => hPQ a (Finset.mem_insert_of_mem ha))
      · have hq : Q ∉ D.poolPinSet pin := fun h => hp (hpinEq.mpr h)
        simp only [if_neg hp, if_neg hq]
    have hscope : (insert slot S).card ≤ q + 1 :=
      (Finset.card_insert_le slot S).trans (Nat.add_le_add_right hs 1)
    have hcomp := hglobal (insert slot S) hscope test hnonneg hlocal
    change (FinLaw.cond (permPoolLaw D.G hpools) (D.poolPinSet pin) hpin).E f ≤ _
    rw [cond_E, cond_E, hmass]
    have hdiv := div_le_div_of_nonneg_right hcomp hid.le
    simpa only [test, mul_div_assoc] using hdiv

end PC
end HypercubeRamsey.S18.Lane_sol_d18l_row
