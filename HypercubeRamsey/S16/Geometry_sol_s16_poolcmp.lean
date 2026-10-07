import HypercubeRamsey.PartC.LowMode
import HypercubeRamsey.S16.Geometry_q_s16_geom
import Mathlib.Logic.Equiv.Fintype

namespace HypercubeRamsey.Lane_sol_s16_poolcmp

open Classical
open scoped BigOperators

private theorem law_ext {Ω : Type*} [Fintype Ω] {P Q : FinLaw Ω}
    (h : P.w = Q.w) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- A finite marginal invariant under a transitive action is uniform. -/
theorem map_uniform_of_symmetry {Ω X : Type*} [Fintype Ω] [Fintype X]
    [DecidableEq X] (P : FinLaw Ω) (R : Ω → X) (T : Finset X) (hT : T.Nonempty)
    (hsupport : ∀ ω, P.w ω ≠ 0 → R ω ∈ T)
    (htrans : ∀ x ∈ T, ∀ y ∈ T, ∃ e : Ω ≃ Ω,
      (∀ ω, P.w (e ω) = P.w ω) ∧ (∀ ω, R (e ω) = y ↔ R ω = x)) :
    FinLaw.map P R = FinLaw.uniform T hT := by
  classical
  let M := FinLaw.map P R
  have hoff (x : X) (hx : x ∉ T) : M.w x = 0 := by
    apply Finset.sum_eq_zero
    intro ω _
    by_cases hr : R ω = x
    · have hw : P.w ω = 0 := by
        by_contra h
        exact hx (hr ▸ hsupport ω h)
      simp [hr, hw]
    · simp [hr]
  have hequal (x : X) (hx : x ∈ T) (y : X) (hy : y ∈ T) : M.w y = M.w x := by
    obtain ⟨e, hw, hr⟩ := htrans x hx y hy
    change (∑ ω, if R ω = y then P.w ω else 0) =
      ∑ ω, if R ω = x then P.w ω else 0
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro ω _
    simp only [hw, hr]
  let x := hT.choose
  have hx : x ∈ T := hT.choose_spec
  have hsum : (T.card : ℝ) * M.w x = 1 := by
    calc
      (T.card : ℝ) * M.w x = ∑ y ∈ T, M.w y := by
        rw [Finset.sum_congr rfl (fun y hy => hequal x hx y hy), Finset.sum_const,
          nsmul_eq_mul]
      _ = ∑ y, M.w y := by
        apply Finset.sum_subset (Finset.subset_univ T)
        intro y _ hy
        exact hoff y hy
      _ = 1 := M.sum_one
  have hc : (T.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hT).ne'
  have hweight : M.w x = 1 / (T.card : ℝ) := by
    apply (eq_div_iff hc).2
    simpa [mul_comm] using hsum
  have hw : M.w = (FinLaw.uniform T hT).w := by
    funext y
    by_cases hy : y ∈ T
    · change M.w y = if y ∈ T then 1 / (T.card : ℝ) else 0
      rw [ite_eq_left hy]
      exact (hequal x hx y hy).trans hweight
    · change M.w y = if y ∈ T then 1 / (T.card : ℝ) else 0
      rw [ite_eq_right hy]
      exact hoff y hy
  exact law_ext hw

/-- Expectation commutes with a finite pushforward. -/
theorem map_E {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]
    (P : FinLaw Ω) (R : Ω → X) (f : X → ℝ) :
    (FinLaw.map P R).E f = P.E (fun ω => f (R ω)) := by
  classical
  unfold FinLaw.E FinLaw.map
  simp only
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

/-- A nonnegative local test factors through its restriction map. -/
theorem factor_test {Ω X : Type*} (R : Ω → X) (F : Ω → ℝ)
    (hF : ∀ ω, 0 ≤ F ω) (hlocal : ∀ a b, R a = R b → F a = F b) :
    ∃ f : X → ℝ, (∀ x, 0 ≤ f x) ∧ ∀ ω, F ω = f (R ω) := by
  classical
  let f : X → ℝ := fun x => if h : ∃ ω, R ω = x then F h.choose else 0
  refine ⟨f, ?_, ?_⟩
  · intro x
    dsimp [f]
    split_ifs
    · exact hF _
    · exact le_rfl
  · intro ω
    have h : ∃ a, R a = R ω := ⟨ω, rfl⟩
    simp only [f, dite_eq_left h]
    exact hlocal _ _ h.choose_spec.symm

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}

abbrev Slot (G : LowGeom PT) := Σ c : G.Cell, Fin (G.nslot c)
abbrev Pools (G : LowGeom PT) := ∀ c, CellPool G c

/-- Relabel every bin by a permutation depending on its patch. -/
noncomputable def relabel (G : LowGeom PT)
    (e : ∀ i, Equiv.Perm (Bin PT.tiling i)) : Pools G ≃ Pools G where
  toFun P c s := e _ (P c s)
  invFun P c s := (e _).symm (P c s)
  left_inv P := by funext c s; exact (e _).symm_apply_apply _
  right_inv P := by funext c s; exact (e _).apply_symm_apply _

/-- Relabel slots independently, for the iid law. -/
noncomputable def relabelSlots (G : LowGeom PT)
    (e : ∀ c, ∀ s : Fin (G.nslot c), Equiv.Perm (Bin PT.tiling (G.cellPatch c))) :
    Pools G ≃ Pools G where
  toFun P c s := e c s (P c s)
  invFun P c s := (e c s).symm (P c s)
  left_inv P := by funext c s; exact (e c s).symm_apply_apply _
  right_inv P := by funext c s; exact (e c s).apply_symm_apply _

theorem relabel_mem (G : LowGeom PT) (e : ∀ i, Equiv.Perm (Bin PT.tiling i))
    (P : Pools G) : relabel G e P ∈ permPools G ↔ P ∈ permPools G := by
  classical
  have forward (e : ∀ i, Equiv.Perm (Bin PT.tiling i)) (P : Pools G)
      (hP : P ∈ permPools G) : relabel G e P ∈ permPools G := by
    simp only [permPools, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    intro c c' s s' hp hv
    apply hP c c' s s' hp
    have aux {i j : Fin PT.tiling.m} (h : i = j)
        (x : Bin PT.tiling i) (y : Bin PT.tiling j)
        (hv : (e i x).val = (e j y).val) : x.val = y.val := by
      cases h
      exact congrArg Subtype.val ((e i).injective (Subtype.ext hv))
    exact aux hp _ _ hv
  constructor
  · intro h
    have := forward (fun i => (e i).symm) (relabel G e P) h
    simpa [relabel] using this
  · exact forward e P

/-- Cast a slot's physical bin into the common patch of a scope. -/
noncomputable def restrict (G : LowGeom PT) (i : Fin PT.tiling.m)
    (S : Finset (Slot G)) (hp : ∀ s ∈ S, G.cellPatch s.1 = i)
    (P : Pools G) : S → Bin PT.tiling i := fun s =>
  ⟨(P s.1.1 s.1.2).val, by
    have aux {j : Fin PT.tiling.m} (h : j = i) (x : Bin PT.tiling j) :
        x.val ∈ (PT.tiling.P i).bins.parts := by
      cases h
      exact x.property
    exact aux (hp s.1 s.2) (P s.1.1 s.1.2)⟩

theorem restrict_injective (G : LowGeom PT) (i : Fin PT.tiling.m)
    (S : Finset (Slot G)) (hp : ∀ s ∈ S, G.cellPatch s.1 = i)
    {P : Pools G} (hP : P ∈ permPools G) : Function.Injective (restrict G i S hp P) := by
  intro s t hst
  have h := (Finset.mem_filter.mp hP).2 s.1.1 t.1.1 s.1.2 t.1.2
    ((hp s.1 s.2).trans (hp t.1 t.2).symm) (congrArg Subtype.val hst)
  apply Subtype.ext
  rcases s with ⟨⟨c, a⟩, hs⟩
  rcases t with ⟨⟨d, b⟩, ht⟩
  dsimp at h
  rcases h with ⟨hcd, hab⟩
  subst d
  have : a = b := Fin.ext hab
  subst b
  rfl


noncomputable def binEquiv {i j : Fin PT.tiling.m} (h : i = j) :
    Bin PT.tiling i ≃ Bin PT.tiling j where
  toFun x := ⟨x.val, by cases h; exact x.property⟩
  invFun x := ⟨x.val, by cases h; exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def onPatch (i : Fin PT.tiling.m) (e : Equiv.Perm (Bin PT.tiling i))
    (j : Fin PT.tiling.m) : Equiv.Perm (Bin PT.tiling j) :=
  if h : j = i then (binEquiv h).trans (e.trans (binEquiv h.symm)) else Equiv.refl _

theorem onPatch_val (i j : Fin PT.tiling.m) (h : j = i)
    (e : Equiv.Perm (Bin PT.tiling i)) (x : Bin PT.tiling j) :
    (onPatch i e j x).val = (e (binEquiv h x)).val := by
  subst j
  simp only [onPatch, dite_eq_left rfl, Equiv.trans_apply]
  rfl

theorem restrict_relabel (G : LowGeom PT) (i : Fin PT.tiling.m)
    (S : Finset (Slot G)) (hp : ∀ s ∈ S, G.cellPatch s.1 = i)
    (e : Equiv.Perm (Bin PT.tiling i)) (P : Pools G) :
    restrict G i S hp (relabel G (onPatch i e) P) =
      fun s => e (restrict G i S hp P s) := by
  funext s
  apply Subtype.ext
  exact onPatch_val i _ (hp s.1 s.2) e _

theorem perm_weight_relabel (G : LowGeom PT) (h : (permPools G).Nonempty)
    (e : ∀ i, Equiv.Perm (Bin PT.tiling i)) (P : Pools G) :
    (permPoolLaw G h).w (relabel G e P) = (permPoolLaw G h).w P := by
  simp only [permPoolLaw, FinLaw.uniform, relabel_mem]

/-- The permutation marginal is uniform on all injective restrictions. -/
theorem perm_marginal (G : LowGeom PT) (h : (permPools G).Nonempty)
    (i : Fin PT.tiling.m) (S : Finset (Slot G))
    (hp : ∀ s ∈ S, G.cellPatch s.1 = i) :
    ∃ hInj : (Finset.univ.filter (fun f : S → Bin PT.tiling i => Function.Injective f)).Nonempty,
      FinLaw.map (permPoolLaw G h) (restrict G i S hp) =
        FinLaw.uniform (Finset.univ.filter (fun f : S → Bin PT.tiling i =>
          Function.Injective f)) hInj := by
  classical
  let U := Finset.univ.filter (fun f : S → Bin PT.tiling i => Function.Injective f)
  have hU : U.Nonempty := ⟨restrict G i S hp h.choose, by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    exact restrict_injective G i S hp h.choose_spec⟩
  refine ⟨hU, map_uniform_of_symmetry _ _ U hU ?_ ?_⟩
  · intro P hw
    have hP : P ∈ permPools G := by
      by_contra hP
      exact hw (by simp [permPoolLaw, FinLaw.uniform, hP])
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, restrict_injective G i S hp hP⟩
  · intro x hx y hy
    obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair x y
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    refine ⟨relabel G (onPatch i e), perm_weight_relabel G h _, ?_⟩
    intro P
    rw [restrict_relabel]
    constructor
    · intro hxy
      funext s
      apply e.injective
      rw [he]
      exact congrFun hxy s
    · intro hxy
      funext s
      rw [hxy, he]

noncomputable def scopePerm (G : LowGeom PT) (i : Fin PT.tiling.m)
    (S : Finset (Slot G)) (x y : S → Bin PT.tiling i)
    (c : G.Cell) (s : Fin (G.nslot c)) : Equiv.Perm (Bin PT.tiling (G.cellPatch c)) :=
  if h : (⟨c, s⟩ : Slot G) ∈ S then
    onPatch i (Equiv.swap (x ⟨⟨c, s⟩, h⟩) (y ⟨⟨c, s⟩, h⟩)) (G.cellPatch c)
  else Equiv.refl _

theorem restrict_relabelSlots (G : LowGeom PT) (i : Fin PT.tiling.m)
    (S : Finset (Slot G)) (hp : ∀ s ∈ S, G.cellPatch s.1 = i)
    (x y : S → Bin PT.tiling i) (P : Pools G) :
    restrict G i S hp (relabelSlots G (scopePerm G i S x y) P) =
      fun s => Equiv.swap (x s) (y s) (restrict G i S hp P s) := by
  funext s
  apply Subtype.ext
  change (scopePerm G i S x y s.1.1 s.1.2 (P s.1.1 s.1.2)).val = _
  simp only [scopePerm, dite_eq_left s.2]
  exact onPatch_val i _ (hp s.1 s.2) _ _

/-- The iid marginal is uniform on all restrictions. -/
theorem iid_marginal (G : LowGeom PT) (h : (permPools G).Nonempty)
    (i : Fin PT.tiling.m) (S : Finset (Slot G))
    (hp : ∀ s ∈ S, G.cellPatch s.1 = i) :
    FinLaw.map (iidPoolLaw G h) (restrict G i S hp) =
      FinLaw.uniform Finset.univ ⟨restrict G i S hp h.choose, Finset.mem_univ _⟩ := by
  classical
  apply map_uniform_of_symmetry
  · intro _ _
    exact Finset.mem_univ _
  · intro x _ y _
    refine ⟨relabelSlots G (scopePerm G i S x y), ?_, ?_⟩
    · intro P
      simp [iidPoolLaw, FinLaw.uniform]
    · intro P
      rw [restrict_relabelSlots]
      constructor
      · intro hxy
        funext s
        have hs := congrFun hxy s
        exact (Equiv.swap (x s) (y s)).injective
          (hs.trans (Equiv.swap_apply_left _ _).symm)
      · intro hxy
        funext s
        rw [hxy]
        exact Equiv.swap_apply_left _ _

/-- The exact cardinality of the injective restriction support. -/
theorem inj_support_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [DecidablePred (fun f : α → β => Function.Injective f)] :
    (Finset.univ.filter fun f : α → β => Function.Injective f).card =
      (Fintype.card β).descFactorial (Fintype.card α) := by
  classical
  let e : {f : α → β // Function.Injective f} ≃ (α ↪ β) :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  calc
    _ = Fintype.card {f : α → β // Function.Injective f} := by
      symm
      exact Fintype.card_subtype _
    _ = Fintype.card (α ↪ β) := Fintype.card_congr e
    _ = _ := Fintype.card_embedding_eq

/-- Domination for any nonnegative test on a single patch scope. -/
theorem local_compare (G : LowGeom PT) (h : (permPools G).Nonempty)
    (i : Fin PT.tiling.m) (S : Finset (Slot G))
    (hp : ∀ s ∈ S, G.cellPatch s.1 = i)
    (hg : 2 * S.card ^ 2 ≤ Fintype.card (Bin PT.tiling i))
    (hB : 0 < Fintype.card (Bin PT.tiling i))
    (F : Pools G → ℝ) (hF : ∀ P, 0 ≤ F P)
    (hl : ∀ P Q, (∀ s ∈ S, P s.1 s.2 = Q s.1 s.2) → F P = F Q) :
    (permPoolLaw G h).E F ≤
      (1 + (S.card : ℝ)^2 / Fintype.card (Bin PT.tiling i)) * (iidPoolLaw G h).E F := by
  classical
  let R := restrict G i S hp
  obtain ⟨f, hf, hfactor⟩ := factor_test R F hF (by
    intro P Q hR
    apply hl P Q
    intro s hs
    apply Subtype.ext
    exact congrArg (fun b : Bin PT.tiling i => b.val) (congrFun hR ⟨s, hs⟩))
  have hFdef : F = fun P => f (R P) := funext hfactor
  obtain ⟨hU, hperm⟩ := perm_marginal G h i S hp
  have hiid := iid_marginal G h i S hp
  rw [hFdef, ← map_E (permPoolLaw G h) R f, ← map_E (iidPoolLaw G h) R f]
  change (FinLaw.map (permPoolLaw G h) (restrict G i S hp)).E f ≤ _
  rw [hperm, hiid]
  let U := Finset.univ.filter (fun a : S → Bin PT.tiling i => Function.Injective a)
  have hI : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hU
  have hpow : (0 : ℝ) < (Fintype.card (Bin PT.tiling i) : ℝ) ^ S.card := by positivity
  have hsum : (∑ a ∈ U, f a) ≤ ∑ a, f a := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hf a)
  have hsum0 : 0 ≤ ∑ a : S → Bin PT.tiling i, f a := Finset.sum_nonneg fun a _ => hf a
  have hUcard : U.card = (Fintype.card (Bin PT.tiling i)).descFactorial S.card := by
    simpa only [U, Fintype.card_coe] using
      (inj_support_card (α := S) (β := Bin PT.tiling i))
  have hratio : (Fintype.card (Bin PT.tiling i) : ℝ) ^ S.card / (U.card : ℝ) ≤
      1 + (S.card : ℝ)^2 / Fintype.card (Bin PT.tiling i) := by
    rw [hUcard]
    exact Lane_q_s16_geom.descFactorial_ratio_bound hg
  have hcoef : 1 / (U.card : ℝ) ≤
      (1 + (S.card : ℝ)^2 / Fintype.card (Bin PT.tiling i)) /
        (Fintype.card (Bin PT.tiling i) : ℝ) ^ S.card := by
    apply (div_le_div_iff₀ hI hpow).2
    simpa only [one_mul] using (div_le_iff₀ hI).mp hratio
  have hEU : (FinLaw.uniform U hU).E f = (∑ a ∈ U, f a) / (U.card : ℝ) := by
    simp only [FinLaw.E, FinLaw.uniform]
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
    ring
  have hEV : (FinLaw.uniform Finset.univ
      ⟨R h.choose, Finset.mem_univ _⟩).E f =
      (∑ a, f a) / (Fintype.card (Bin PT.tiling i) : ℝ) ^ S.card := by
    simp only [FinLaw.E, FinLaw.uniform, Finset.mem_univ, ite_true]
    rw [← Finset.mul_sum]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Nat.cast_pow]
    ring
  rw [hEU, hEV]
  calc
    _ ≤ (∑ a, f a) / (U.card : ℝ) := div_le_div_of_nonneg_right hsum hI.le
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hcoef hsum0
      convert hh using 1 <;> ring


/-- Every individual slot has a uniform bin marginal in a relabeling-invariant law. -/
theorem slot_uniform (G : LowGeom PT) (P : FinLaw (Pools G))
    (hInv : ∀ e : ∀ i, Equiv.Perm (Bin PT.tiling i), ∀ ω,
      P.w (relabel G e ω) = P.w ω)
    (c : G.Cell) (s : Fin (G.nslot c)) (D : Bin PT.tiling (G.cellPatch c)) :
    FinLaw.map P (fun ω => ω c s) =
      FinLaw.uniform Finset.univ ⟨D, Finset.mem_univ _⟩ := by
  classical
  apply map_uniform_of_symmetry
  · intro _ _
    exact Finset.mem_univ _
  · intro x _ y _
    let e := Equiv.swap x y
    refine ⟨relabel G (onPatch (G.cellPatch c) e), hInv _, ?_⟩
    intro ω
    have hv : relabel G (onPatch (G.cellPatch c) e) ω c s = e (ω c s) := by
      change onPatch (G.cellPatch c) e (G.cellPatch c) (ω c s) = e (ω c s)
      simp only [onPatch, dite_eq_left rfl, Equiv.trans_apply]
      rfl
    rw [hv]
    constructor
    · intro h
      exact e.injective (h.trans (Equiv.swap_apply_left x y).symm)
    · intro h
      rw [h]
      exact Equiv.swap_apply_left x y

/-- The two pool laws assign the same probability to each single-slot pin. -/
theorem pin_mass_equal (G : LowGeom PT) (h : (permPools G).Nonempty)
    (c : G.Cell) (s : Fin (G.nslot c)) (D : Bin PT.tiling (G.cellPatch c)) :
    (∑ P ∈ Finset.univ.filter (fun P : Pools G => P c s = D), (permPoolLaw G h).w P) =
      ∑ P ∈ Finset.univ.filter (fun P : Pools G => P c s = D), (iidPoolLaw G h).w P := by
  classical
  have hperm := slot_uniform G (permPoolLaw G h) (perm_weight_relabel G h) c s D
  have hiid := slot_uniform G (iidPoolLaw G h) (by
    intro e P
    simp [iidPoolLaw, FinLaw.uniform]) c s D
  have hw := congrArg (fun L : FinLaw (Bin PT.tiling (G.cellPatch c)) => L.w D)
    (hperm.trans hiid.symm)
  simpa [FinLaw.map, Finset.sum_filter] using hw

/-- Conditioning is the normalized expectation of the event indicator. -/
theorem cond_E {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (P : FinLaw Ω) (A : Finset Ω)
    (hA : 0 < ∑ ω ∈ A, P.w ω) (F : Ω → ℝ) :
    (FinLaw.cond P A hA).E F =
      P.E (fun ω => if ω ∈ A then F ω else 0) / (∑ ω ∈ A, P.w ω) := by
  classical
  unfold FinLaw.E FinLaw.cond
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  dsimp only
  split_ifs <;> ring

/-- Retaining a global pin reduces comparison to the scope with that slot inserted. -/
theorem local_compare_pinned (G : LowGeom PT) (h : (permPools G).Nonempty)
    (i : Fin PT.tiling.m) (S : Finset (Slot G))
    (hp : ∀ s ∈ S, G.cellPatch s.1 = i)
    (s : Slot G) (D : Bin PT.tiling (G.cellPatch s.1)) (hs : G.cellPatch s.1 = i)
    (hg : 2 * (insert s S).card ^ 2 ≤ Fintype.card (Bin PT.tiling i))
    (hB : 0 < Fintype.card (Bin PT.tiling i))
    (F : Pools G → ℝ) (hF : ∀ P, 0 ≤ F P)
    (hl : ∀ P Q, (∀ s ∈ S, P s.1 s.2 = Q s.1 s.2) → F P = F Q)
    (hpermPin : 0 < ∑ P ∈ Finset.univ.filter (fun P : Pools G => P s.1 s.2 = D),
      (permPoolLaw G h).w P)
    (hiidPin : 0 < ∑ P ∈ Finset.univ.filter (fun P : Pools G => P s.1 s.2 = D),
      (iidPoolLaw G h).w P) :
    (FinLaw.cond (permPoolLaw G h)
      (Finset.univ.filter (fun P : Pools G => P s.1 s.2 = D)) hpermPin).E F ≤
      (1 + ((insert s S).card : ℝ)^2 / Fintype.card (Bin PT.tiling i)) *
      (FinLaw.cond (iidPoolLaw G h)
        (Finset.univ.filter (fun P : Pools G => P s.1 s.2 = D)) hiidPin).E F := by
  classical
  let A := Finset.univ.filter (fun P : Pools G => P s.1 s.2 = D)
  let Fpin : Pools G → ℝ := fun P => if P ∈ A then F P else 0
  have hscope : ∀ t ∈ insert s S, G.cellPatch t.1 = i := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hs
    · exact hp t ht
  have hFpin : ∀ P, 0 ≤ Fpin P := by
    intro P
    dsimp [Fpin]
    split_ifs
    · exact hF P
    · exact le_rfl
  have hlocal : ∀ P Q, (∀ t ∈ insert s S, P t.1 t.2 = Q t.1 t.2) → Fpin P = Fpin Q := by
    intro P Q hPQ
    have hv := hPQ s (Finset.mem_insert_self s S)
    have hf := hl P Q (fun t ht => hPQ t (Finset.mem_insert_of_mem ht))
    simp [Fpin, A, hv, hf]
  have hcmp := local_compare G h i (insert s S) hscope hg hB Fpin hFpin hlocal
  have hmass := pin_mass_equal G h s.1 s.2 D
  rw [cond_E (permPoolLaw G h) A hpermPin F, cond_E (iidPoolLaw G h) A hiidPin F]
  change (permPoolLaw G h).E Fpin / (∑ P ∈ A, (permPoolLaw G h).w P) ≤
    (1 + ((insert s S).card : ℝ)^2 / Fintype.card (Bin PT.tiling i)) *
      ((iidPoolLaw G h).E Fpin / (∑ P ∈ A, (iidPoolLaw G h).w P))
  rw [hmass]
  have hh := div_le_div_of_nonneg_right hcmp hiidPin.le
  simpa only [mul_div_assoc] using hh

end HypercubeRamsey.Lane_sol_s16_poolcmp
