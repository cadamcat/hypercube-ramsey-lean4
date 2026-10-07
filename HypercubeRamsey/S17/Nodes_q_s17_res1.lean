import HypercubeRamsey.S17.Needs
import HypercubeRamsey.Framework.FinProbLemmas
import HypercubeRamsey.S03.Clock.Inputs_p_clock_r1

namespace HypercubeRamsey.Lane_q_s17_res1

open Classical

private noncomputable def toFinProbLaw {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) : FinProb Ω where
  w := P.w
  nonneg := P.nonneg
  sum_eq_one := P.sum_one

private theorem finLaw_ext_of_weights {Ω : Type*} [Fintype Ω]
    {P Q : FinLaw Ω} (h : P.w = Q.w) : P = Q := by
  cases P with
  | mk w hw hs =>
      cases Q with
      | mk w' hw' hs' =>
          change w = w' at h
          subst w'
          rfl

/-- A product of tests on disjoint coordinate sets has exactly the product
of its one-test probabilities. -/
private theorem pi_expect_prod_disjoint
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (s : Finset J) (f : J → (∀ i, Ω i) → ℝ) (A : J → Finset ι)
    (hdep : ∀ j, FinProb.DependsOn (f j) (A j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    (FinLaw.pi P).E (fun x => ∏ j ∈ s, f j x) =
      ∏ j ∈ s, (FinLaw.pi P).E (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change (FinLaw.pi P).E (fun _ => 1) = 1
      unfold FinLaw.E
      simpa using (FinLaw.pi P).sum_one
  | @insert a s ha ih =>
      have hprodDep : FinProb.DependsOn
          (fun x => ∏ j ∈ s, f j x) (s.biUnion A) := by
        intro x y hxy
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j
        intro i hi
        exact hxy i (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)
      have hdisjUnion : Disjoint (A a) (s.biUnion A) := by
        apply Finset.disjoint_left.mpr
        intro i hi hmem
        rcases Finset.mem_biUnion.mp hmem with ⟨j, hj, hji⟩
        exact (Finset.disjoint_left.mp (hdisj a j (by
          intro h
          subst j
          exact ha hj))) hi hji
      have hmul := FinProb.pi_expect_mul_of_disjoint
        (fun i => toFinProbLaw (P i)) (f a) (fun x => ∏ j ∈ s, f j x)
        (A a) (s.biUnion A) (hdep a) hprodDep hdisjUnion
      have hfactor (x : ∀ i, Ω i) :
          (∏ j ∈ insert a s, f j x) = f a x * ∏ j ∈ s, f j x :=
        Finset.prod_insert ha
      have hleft : (FinLaw.pi P).E
          (fun x => ∏ j ∈ insert a s, f j x) =
          (FinLaw.pi P).E (fun x => f a x * ∏ j ∈ s, f j x) := by
        unfold FinLaw.E
        apply Finset.sum_congr rfl
        intro x hx
        dsimp
        rw [hfactor x]
      have hright :
          (∏ j ∈ insert a s, (FinLaw.pi P).E (f j)) =
            (FinLaw.pi P).E (f a) * ∏ j ∈ s, (FinLaw.pi P).E (f j) :=
        Finset.prod_insert ha
      have hmulLaw : (FinLaw.pi P).E
          (fun x => f a x * ∏ j ∈ s, f j x) =
          (FinLaw.pi P).E (f a) *
            (FinLaw.pi P).E (fun x => ∏ j ∈ s, f j x) := by
        simpa [FinLaw.E, FinProb.expect, FinLaw.pi, FinProb.pi, toFinProbLaw] using hmul
      calc
        (FinLaw.pi P).E (fun x => ∏ j ∈ insert a s, f j x) =
            (FinLaw.pi P).E (fun x => f a x * ∏ j ∈ s, f j x) := hleft
        _ = (FinLaw.pi P).E (f a) *
            (FinLaw.pi P).E (fun x => ∏ j ∈ s, f j x) := hmulLaw
        _ = (FinLaw.pi P).E (f a) * ∏ j ∈ s, (FinLaw.pi P).E (f j) := by rw [ih]
        _ = ∏ j ∈ insert a s, (FinLaw.pi P).E (f j) := hright.symm

private theorem indicator_prod_eq
    {J Ω : Type*} [Fintype J] [DecidableEq J] (s : Finset J)
    (E : J → Ω → Prop) (x : Ω) :
    (if ∀ j ∈ s, E j x then (1 : ℝ) else 0) =
      ∏ j ∈ s, (if E j x then (1 : ℝ) else 0) := by
  classical
  simpa [Finset.prod_const_one] using
    (Finset.prod_ite_zero (s := s) (p := fun j => E j x)
      (f := fun _ => (1 : ℝ))).symm

/-- The same factorization written for event probabilities. -/
theorem pi_pr_inter_disjoint
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J] [DecidableEq J]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinLaw (Ω i))
    (s : Finset J) (E : J → (∀ i, Ω i) → Prop) (A : J → Finset ι)
    (hdep : ∀ j, FinProb.DependsOn
      (fun x => if E j x then (1 : ℝ) else 0) (A j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    (FinLaw.pi P).pr (fun x => ∀ j ∈ s, E j x) =
      ∏ j ∈ s, (FinLaw.pi P).pr (E j) := by
  classical
  have hpoint (x : ∀ i, Ω i) := indicator_prod_eq s E x
  calc
    (FinLaw.pi P).pr (fun x => ∀ j ∈ s, E j x) =
        (FinLaw.pi P).E (fun x => ∏ j ∈ s,
          (if E j x then (1 : ℝ) else 0)) := by
      unfold FinLaw.pr FinLaw.E
      apply Finset.sum_congr rfl
      intro x hx
      dsimp
      rw [← hpoint x]
      by_cases h : ∀ j ∈ s, E j x <;> simp [h]
    _ = ∏ j ∈ s, (FinLaw.pi P).E
        (fun x => if E j x then (1 : ℝ) else 0) :=
      pi_expect_prod_disjoint P s
        (fun j x => if E j x then (1 : ℝ) else 0) A hdep hdisj
    _ = ∏ j ∈ s, (FinLaw.pi P).pr (E j) := by
      apply Finset.prod_congr rfl
      intro j hj
      unfold FinLaw.E FinLaw.pr
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : E j x <;> simp [h]

/-- Mapping each independent coordinate separately preserves the product law. -/
theorem pi_map_law
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω Ξ : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Ξ i)]
    (P : ∀ i, FinLaw (Ω i)) (f : ∀ i, Ω i → Ξ i) :
    FinLaw.map (FinLaw.pi P) (fun x i => f i (x i)) =
      FinLaw.pi (fun i => FinLaw.map (P i) (f i)) := by
  classical
  let L := FinLaw.map (FinLaw.pi P) (fun x i => f i (x i))
  let R := FinLaw.pi (fun i => FinLaw.map (P i) (f i))
  have hweight : L.w = R.w := by
    funext y
    change (∑ x : ∀ i, Ω i,
        if (fun i => f i (x i)) = y then ∏ i, (P i).w (x i) else 0) =
      ∏ i, ∑ z : Ω i, if f i z = y i then (P i).w z else 0
    have hterm (x : ∀ i, Ω i) :
        (if (fun i => f i (x i)) = y then ∏ i, (P i).w (x i) else 0) =
          ∏ i, (if f i (x i) = y i then (P i).w (x i) else 0) := by
      by_cases h : (fun i => f i (x i)) = y
      · have heq : ∀ i, f i (x i) = y i := fun i => congrFun h i
        simp [h, heq]
      · have hnot : ¬ ∀ i, f i (x i) = y i := by
          intro hall
          apply h
          funext i
          exact hall i
        push_neg at hnot
        obtain ⟨i, hi⟩ := hnot
        have hz : ∏ i, (if f i (x i) = y i then (P i).w (x i) else 0) = 0 := by
          exact Finset.prod_eq_zero (s := Finset.univ)
            (f := fun i => if f i (x i) = y i then (P i).w (x i) else 0)
            (Finset.mem_univ i) (by simp [hi])
        simp [h, hz]
    calc
      _ = ∑ x : ∀ i, Ω i, ∏ i, (if f i (x i) = y i then (P i).w (x i) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hterm x
      _ = ∏ i, ∑ z : Ω i, if f i z = y i then (P i).w z else 0 := by
        exact (Fintype.prod_sum
          (fun i (z : Ω i) => if f i z = y i then (P i).w z else 0)).symm
  exact finLaw_ext_of_weights hweight

/-- Coordinate marginals of a product law, in the Section 17 law vocabulary. -/
theorem pi_marginal_law
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (s : Finset ι) :
    FinLaw.map (FinLaw.pi P) (fun x (i : {i // i ∈ s}) => x i.1) =
      FinLaw.pi (fun i : {i // i ∈ s} => P i.1) := by
  classical
  let L := FinLaw.map (FinLaw.pi P) (fun x (i : {i // i ∈ s}) => x i.1)
  let R := FinLaw.pi (fun i : {i // i ∈ s} => P i.1)
  have hweight : L.w = R.w := by
    funext x
    exact FinProb.pi_marginal (fun i => toFinProbLaw (P i)) s x
  exact finLaw_ext_of_weights hweight

theorem map_pr_law {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (E : β → Prop) :
    (FinLaw.map P f).pr E = P.pr (fun x => E (f x)) := by
  classical
  have h := FinProb.map_expect (toFinProbLaw P) f
    (fun y => if E y then (1 : ℝ) else 0)
  simpa [FinLaw.map, FinLaw.pr, FinProb.map, FinProb.expect, FinProb.pr,
    toFinProbLaw] using h

private theorem pi_pr_coordinate_event
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinLaw (Ω i)) (i : ι) (E : Ω i → Prop) :
    (FinLaw.pi P).pr (fun x => E (x i)) = (P i).pr E := by
  classical
  have hpoint (y : Ω i) : (FinLaw.pi P).pr (fun x => x i = y) = (P i).w y := by
    simpa [FinLaw.pr, FinProb.pr, FinLaw.pi, FinProb.pi, toFinProbLaw] using
      Clock.pi_pr_coordinate (fun j => toFinProbLaw (P j)) i y
  have hsplit (x : ∀ j, Ω j) :
      (if E (x i) then (FinLaw.pi P).w x else 0) =
        ∑ y : Ω i, (if E y ∧ x i = y then (FinLaw.pi P).w x else 0) := by
    have hterm (y : Ω i) :
        (if E y ∧ x i = y then (FinLaw.pi P).w x else 0) =
          (if y = x i then (if E (x i) then (FinLaw.pi P).w x else 0) else 0) := by
      by_cases hy : y = x i <;> simp [hy, eq_comm]
    symm
    calc
      ∑ y : Ω i, (if E y ∧ x i = y then (FinLaw.pi P).w x else 0) =
          ∑ y : Ω i, (if y = x i then
            (if E (x i) then (FinLaw.pi P).w x else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hterm y
      _ = if E (x i) then (FinLaw.pi P).w x else 0 := by simp
  calc
    (FinLaw.pi P).pr (fun x => E (x i)) =
        ∑ x : (∀ j, Ω j), ∑ y : Ω i,
          (if E y ∧ x i = y then (FinLaw.pi P).w x else 0) := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro x hx
      exact hsplit x
    _ = ∑ y : Ω i, ∑ x : (∀ j, Ω j),
        if E y ∧ x i = y then (FinLaw.pi P).w x else 0 := Finset.sum_comm
    _ = ∑ y : Ω i, if E y then
        (FinLaw.pi P).pr (fun x => x i = y) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hEy : E y <;> simp [hEy, FinLaw.pr]
    _ = ∑ y : Ω i, if E y then (P i).w y else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hEy : E y <;> simp [hEy, hpoint y]
    _ = (P i).pr E := rfl

/-- Push a product law through an injectively selected family of coordinates. -/
theorem pi_map_injective
    {ι C : Type*} [Fintype ι] [DecidableEq ι] [Fintype C] [DecidableEq C]
    {Ω : ι → Type*} {Ξ : C → Type*}
    [∀ i, Fintype (Ω i)] [∀ c, Fintype (Ξ c)]
    (P : ∀ i, FinLaw (Ω i)) (g : C → ι) (hg : Function.Injective g)
    (f : ∀ c, Ω (g c) → Ξ c) :
    FinLaw.map (FinLaw.pi P) (fun x c => f c (x (g c))) =
      FinLaw.pi (fun c => FinLaw.map (P (g c)) (f c)) := by
  classical
  let L := FinLaw.map (FinLaw.pi P) (fun x c => f c (x (g c)))
  let R := FinLaw.pi (fun c => FinLaw.map (P (g c)) (f c))
  have hweight : L.w = R.w := by
    funext y
    have hsingle (c : C) :
        (FinLaw.pi P).pr (fun x => f c (x (g c)) = y c) =
          (FinLaw.map (P (g c)) (f c)).w (y c) := by
      calc
        _ = (P (g c)).pr (fun z => f c z = y c) :=
          pi_pr_coordinate_event P (g c) _
        _ = (FinLaw.map (P (g c)) (f c)).w (y c) := rfl
    have hdep : ∀ c, FinProb.DependsOn
        (fun x => if f c (x (g c)) = y c then (1 : ℝ) else 0) {g c} := by
      intro c x x' hxy
      have hx := hxy (g c) (by simp)
      simp [hx]
    have hdisj : ∀ c d, c ≠ d → Disjoint ({g c} : Finset ι) {g d} := by
      intro c d hcd
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      simp only [Finset.mem_singleton] at hz hz'
      exact hcd (hg (hz.symm.trans hz'))
    have hfac := pi_pr_inter_disjoint P Finset.univ
      (fun c x => f c (x (g c)) = y c) (fun c => {g c}) hdep hdisj
    change (FinLaw.pi P).pr
        (fun x => ∀ c ∈ (Finset.univ : Finset C), f c (x (g c)) = y c) = _ at hfac
    calc
      L.w y = (FinLaw.pi P).pr
          (fun x => ∀ c ∈ (Finset.univ : Finset C), f c (x (g c)) = y c) := by
        simp [L, FinLaw.map, FinLaw.pr, FinLaw.pi, funext_iff]
      _ = ∏ c ∈ (Finset.univ : Finset C),
          (FinLaw.pi P).pr (fun x => f c (x (g c)) = y c) := hfac
      _ = ∏ c ∈ (Finset.univ : Finset C),
          (FinLaw.map (P (g c)) (f c)).w (y c) := by
        apply Finset.prod_congr rfl
        intro c hc
        exact hsingle c
      _ = R.w y := rfl
  exact finLaw_ext_of_weights hweight

abbrev TapeRoundIndex {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {G : LowGeom PT} (Ts : ℕ) :=
  Σ C : G.Cell, Fin (Ts + 2)

def flattenTapesEquiv
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} (F : FreshCell G) (Ts : ℕ) :
    Tapes F Ts ≃ (∀ i : TapeRoundIndex (G := G) Ts, TapeEntry F i.1) where
  toFun tapes i := tapes i.1 i.2
  invFun flat C r := flat ⟨C, r⟩
  left_inv := by intro tapes; funext C r; rfl
  right_inv := by intro flat; funext i; cases i; rfl

noncomputable def flatTapeLaw
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} (F : FreshCell G) (Ts : ℕ) :
    FinLaw (∀ i : TapeRoundIndex (G := G) Ts, TapeEntry F i.1) :=
  FinLaw.pi fun i => FinLaw.pi fun P : F.Pool i.1 => F.fresh i.1 P

theorem tapeLaw_flatten
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {G : LowGeom PT} (F : FreshCell G) (Ts : ℕ) :
    FinLaw.map (tapeLaw F Ts) (flattenTapesEquiv F Ts) = flatTapeLaw F Ts := by
  classical
  let e := flattenTapesEquiv F Ts
  let L := FinLaw.map (tapeLaw F Ts) e
  let R := flatTapeLaw F Ts
  have hweight : L.w = R.w := by
    funext x
    have hsum : (∑ tapes : Tapes F Ts,
        if e tapes = x then (tapeLaw F Ts).w tapes else 0) =
        (tapeLaw F Ts).w (e.symm x) := by
      rw [← Equiv.sum_comp e.symm]
      simp only [Equiv.apply_symm_apply]
      rw [Finset.sum_ite_eq' Finset.univ x]
      simp
    change (∑ tapes : Tapes F Ts,
        if e tapes = x then (tapeLaw F Ts).w tapes else 0) = R.w x
    rw [hsum]
    change ∏ C : G.Cell, ∏ r : Fin (Ts + 2), ∏ P : F.Pool C,
        (F.fresh C P).w ((e.symm x) C r P) =
      ∏ i : TapeRoundIndex (G := G) Ts, ∏ P : F.Pool i.1,
        (F.fresh i.1 P).w (x i P)
    rw [← Fintype.prod_sigma']
    rfl
  exact finLaw_ext_of_weights hweight

private theorem graphBall_mono_radius
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed : Finset (Pos T k)) : ∀ {n m : ℕ}, n ≤ m →
      LE.graphBall seed n ⊆ LE.graphBall seed m := by
  intro n m hnm
  induction m generalizing n with
  | zero =>
      have : n = 0 := by omega
      subst n
      exact Finset.Subset.rfl
  | succ m ih =>
      by_cases hn : n ≤ m
      · exact (ih hn).trans (by
          change LE.graphBall seed m ⊆
            LE.graphBall seed m ∪
              Finset.univ.filter (fun w => ∃ v ∈ LE.graphBall seed m, LE.Adjacent w v)
          exact Finset.subset_union_left)
      · have : n = m + 1 := by omega
        subst n
        exact Finset.Subset.rfl

private theorem graphBall_adj_extend
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed : Finset (Pos T k)) {n : ℕ} {v w : Pos T k}
    (hv : v ∈ LE.graphBall seed n) (hadj : LE.Adjacent w v) :
    w ∈ LE.graphBall seed (n + 1) := by
  change w ∈ LE.graphBall seed n ∪
    Finset.univ.filter (fun x => ∃ y ∈ LE.graphBall seed n, LE.Adjacent x y)
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, v, hv, hadj⟩

private theorem graphBall_subset_add
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed other : Finset (Pos T k)) (n : ℕ)
    (hseed : other ⊆ LE.graphBall seed n) :
    ∀ m : ℕ, LE.graphBall other m ⊆ LE.graphBall seed (n + m) := by
  intro m
  induction m with
  | zero =>
      simpa [ListEvent.graphBall] using hseed
  | succ m ih =>
      intro x hx
      rw [ListEvent.graphBall] at hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have hmem := ih hx
        exact graphBall_mono_radius LE seed (by omega) hmem
      · rcases Finset.mem_filter.mp hx with ⟨_, y, hy, hxy⟩
        exact graphBall_adj_extend LE seed (ih hy) hxy

private theorem incident_subset_ball_one
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (C : D.G.Cell) (v : Pos T k) (hCv : C ∈ LE.scope v) :
    LE.incidentEvents C ⊆ LE.graphBall {v} 1 := by
  intro w hw
  have hwC : C ∈ LE.scope w := (Finset.mem_filter.mp hw).2
  by_cases hEq : w = v
  · subst w
    change v ∈ ({v} ∪ Finset.univ.filter (fun x => ∃ y ∈ ({v} : Finset (Pos T k)), LE.Adjacent x y))
    exact Finset.mem_union.mpr (Or.inl (by simp))
  · have hadj : LE.Adjacent w v := by
      refine ⟨hEq, ?_⟩
      intro hdis
      exact (Finset.disjoint_left.mp hdis) hwC hCv
    change w ∈ ({v} ∪ Finset.univ.filter (fun x => ∃ y ∈ ({v} : Finset (Pos T k)), LE.Adjacent x y))
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, v, by simp, hadj⟩

private theorem incident_subset_ball_one_of_root
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (seed : Finset (Pos T k)) (v : Pos T k) (hv : v ∈ seed)
    (C : D.G.Cell) (hCv : C ∈ LE.scope v) :
    LE.incidentEvents C ⊆ LE.graphBall seed 1 := by
  intro w hw
  have hwC : C ∈ LE.scope w := (Finset.mem_filter.mp hw).2
  by_cases hEq : w = v
  · subst w
    change v ∈ seed ∪ Finset.univ.filter (fun x => ∃ y ∈ seed, LE.Adjacent x y)
    exact Finset.mem_union.mpr (Or.inl hv)
  · have hadj : LE.Adjacent w v := by
      refine ⟨hEq, ?_⟩
      intro hdis
      exact (Finset.disjoint_left.mp hdis) hwC hCv
    exact graphBall_adj_extend LE seed hv hadj

private theorem event_mem_incident
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    {C : D.G.Cell} {v : Pos T k} (hCv : C ∈ LE.scope v) :
    v ∈ LE.incidentEvents C := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCv⟩

private theorem run_cell_locality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F)
    (Ts : ℕ) (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    ∀ C, LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆ events →
      (LE.runRounds Ts order Finset.univ pools tapes).1 C =
          (LE.runRounds Ts order events pools tapes).1 C ∧
        (LE.runRounds Ts order Finset.univ pools tapes).2 C =
          (LE.runRounds Ts order events pools tapes).2 C := by
  induction Ts with
  | zero =>
      intro C _
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      intro C hball
      let fullPrev := LE.runRounds n order Finset.univ pools tapes
      let partPrev := LE.runRounds n order events pools tapes
      have hfull : LE.runRounds (n + 1) order Finset.univ pools tapes =
          LE.round order Finset.univ pools tapes fullPrev.1 fullPrev.2 := by
        simp [fullPrev, ListEvent.runRounds]
      have hpart : LE.runRounds (n + 1) order events pools tapes =
          LE.round order events pools tapes partPrev.1 partPrev.2 := by
        simp [partPrev, ListEvent.runRounds]
      have hball' : LE.graphBall (LE.incidentEvents C) (2 * n + 4) ⊆ events := by
        have hr : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
        simpa [hr] using hball
      have hactive (v : Pos T k) (hvC : C ∈ LE.scope v) :
          (v ∈ LE.active order Finset.univ fullPrev.1) ↔
            (v ∈ LE.active order events partPrev.1) := by
        have hvInc : v ∈ LE.incidentEvents C := event_mem_incident LE hvC
        have hvBall0 : v ∈ LE.graphBall (LE.incidentEvents C) 0 := by
          simpa [ListEvent.graphBall] using hvInc
        have hvBall : v ∈ LE.graphBall (LE.incidentEvents C) (2 * n + 4) :=
          graphBall_mono_radius LE _ (by omega) hvBall0
        have hvEvents : v ∈ events := hball' hvBall
        have hscopeState : ∀ x, x ∈ LE.scope v → fullPrev.1 x = partPrev.1 x := by
          intro x hx
          have hseed : LE.incidentEvents x ⊆ LE.graphBall (LE.incidentEvents C) 1 :=
            incident_subset_ball_one_of_root LE (LE.incidentEvents C) v hvInc x hx
          have hlocal := graphBall_subset_add LE (LE.incidentEvents C)
            (LE.incidentEvents x) 1 hseed (2 * n + 2)
          have hsub : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆
              LE.graphBall (LE.incidentEvents C) (2 * n + 3) := by
            have hr : 1 + (2 * n + 2) = 2 * n + 3 := by omega
            rw [hr] at hlocal
            exact hlocal
          have hsub' : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆ events :=
            hsub.trans (fun y hy => hball' (graphBall_mono_radius LE _ (by omega) hy))
          exact (ih x hsub').1
        have hSv : LE.S v fullPrev.1 ↔ LE.S v partPrev.1 :=
          LE.scope_ok v fullPrev.1 partPrev.1 hscopeState
        have hblock (w : Pos T k) (hw : LE.Adjacent w v) :
            (LE.S w fullPrev.1 ↔ LE.S w partPrev.1) := by
          have hvBall0 : v ∈ LE.graphBall (LE.incidentEvents C) 0 := by
            simpa [ListEvent.graphBall] using hvInc
          have hvBallOne := graphBall_adj_extend LE (LE.incidentEvents C) hvBall0 hw
          have hwBall : w ∈ LE.graphBall (LE.incidentEvents C) (2 * n + 4) :=
            graphBall_mono_radius LE _ (by omega) hvBallOne
          have _hwEvents : w ∈ events := hball' hwBall
          have hstate : ∀ x, x ∈ LE.scope w → fullPrev.1 x = partPrev.1 x := by
            intro x hx
            have hseed₁ : LE.incidentEvents x ⊆ LE.graphBall {w} 1 :=
              incident_subset_ball_one LE x w hx
            have hseed₂ : ({w} : Finset (Pos T k)) ⊆
                LE.graphBall (LE.incidentEvents C) 1 := by
              intro y hy
              have : y = w := Finset.mem_singleton.mp hy
              subst y
              exact hvBallOne
            have hseed : LE.incidentEvents x ⊆
                LE.graphBall (LE.incidentEvents C) 2 := by
              have hsub := graphBall_subset_add LE (LE.incidentEvents C) {w} 1 hseed₂ 1
              exact (Finset.Subset.trans hseed₁ hsub)
            have hlocal := graphBall_subset_add LE (LE.incidentEvents C)
              (LE.incidentEvents x) 2 hseed (2 * n + 2)
            have hsub : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆
                LE.graphBall (LE.incidentEvents C) (2 * n + 4) := by
              have hr : 2 + (2 * n + 2) = 2 * n + 4 := by omega
              rw [hr] at hlocal
              exact hlocal
            have hsub' : LE.graphBall (LE.incidentEvents x) (2 * n + 2) ⊆ events :=
              hsub.trans hball'
            exact (ih x hsub').1
          exact LE.scope_ok w fullPrev.1 partPrev.1 hstate
        constructor
        · intro hfullActive
          change v ∈ Finset.univ.filter _ at hfullActive
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfullActive
          rcases hfullActive with ⟨hSvFull, hbeforeFull⟩
          change v ∈ Finset.univ.filter _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hvEvents, hSv.mp hSvFull, ?_⟩
          intro w hwEvents hbefore hwAdj hSwPart
          have hwAdj' : LE.Adjacent w v := hwAdj
          exact (hbeforeFull w trivial hbefore hwAdj')
            ((hblock w hwAdj').mpr hSwPart)
        · intro hpartActive
          change v ∈ Finset.univ.filter _ at hpartActive
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpartActive
          rcases hpartActive with ⟨hvEvents', hSvPart, hbeforePart⟩
          change v ∈ Finset.univ.filter _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hSv.mpr hSvPart, ?_⟩
          intro w _ hbefore hwAdj hSwFull
          have hSwPart := (hblock w hwAdj).mp hSwFull
          have hvBall0 : v ∈ LE.graphBall (LE.incidentEvents C) 0 := by
            simpa [ListEvent.graphBall] using hvInc
          have hwBall := graphBall_adj_extend LE (LE.incidentEvents C) hvBall0 hwAdj
          exact hbeforePart w (hball' (graphBall_mono_radius LE _ (by omega) hwBall))
            hbefore hwAdj hSwPart
      have htouch :
          (∃ v ∈ LE.active order Finset.univ fullPrev.1, C ∈ LE.scope v) ↔
            (∃ v ∈ LE.active order events partPrev.1, C ∈ LE.scope v) := by
        constructor
        · rintro ⟨v, hv, hvC⟩
          exact ⟨v, (hactive v hvC).mp hv, hvC⟩
        · rintro ⟨v, hv, hvC⟩
          exact ⟨v, (hactive v hvC).mpr hv, hvC⟩
      have hprevSubset : LE.graphBall (LE.incidentEvents C) (2 * n + 2) ⊆ events :=
        (graphBall_mono_radius LE _ (by omega)).trans hball'
      have hprev := ih C hprevSubset
      change fullPrev.1 C = partPrev.1 C ∧ fullPrev.2 C = partPrev.2 C at hprev
      rcases hprev with ⟨hprevState, hprevCount⟩
      rw [hfull, hpart]
      simp [ListEvent.round, fullPrev, partPrev, htouch, hprevState, hprevCount]

theorem resampleLocality
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {D : ListGateContext κ T k PT} (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (pools : ∀ C : D.G.Cell, D.F.Pool C)
    (tapes : ∀ C : D.G.Cell, ℕ → TapeEntry D.F C) :
    LE.CellLocalitySpec Ts order pools tapes ∧
      LE.EventTruthLocalitySpec Ts order pools tapes := by
  constructor
  · intro C events hsubset
    have hsmall : LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆ events :=
      (graphBall_mono_radius LE _ (by omega)).trans hsubset
    simpa [ListEvent.resample] using
      (run_cell_locality LE Ts order events pools tapes C hsmall).1
  · intro v events hsubset
    apply LE.scope_ok v _ _
    intro C hC
    have hseed : LE.incidentEvents C ⊆ LE.graphBall {v} 1 :=
      incident_subset_ball_one LE C v hC
    have hball := graphBall_subset_add LE {v} (LE.incidentEvents C) 1 hseed
      (2 * Ts + 2)
    have hsub : LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆
        LE.graphBall {v} (2 * Ts + 3) := by
      have hr : 1 + (2 * Ts + 2) = 2 * Ts + 3 := by omega
      simpa [hr] using hball
    have hevents : LE.graphBall (LE.incidentEvents C) (2 * Ts + 2) ⊆ events :=
      hsub.trans hsubset
    have hfullEq := (run_cell_locality LE Ts order events pools tapes C hevents).1
    simpa [ListEvent.resample] using hfullEq

end HypercubeRamsey.Lane_q_s17_res1
