import HypercubeRamsey.S18.HorizonPool_sol_s18_n5
import HypercubeRamsey.S18.Prefix_sol_s18_n4

namespace HypercubeRamsey.S18.Lane_sol_s18_n5
open Classical
open scoped BigOperators
variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k} {hPT : PT.Valid}

noncomputable def inverseScope {A B : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] (scope : A → Finset B) (b : B) : Finset A :=
  Finset.univ.filter fun a => b ∈ scope a

theorem inverse_comp_card {A B C : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (S : A → Finset B) (R : B → Finset C) (d e : ℕ)
    (hS : ∀ b, (inverseScope S b).card ≤ d)
    (hR : ∀ c, (inverseScope R c).card ≤ e) (c : C) :
    (inverseScope (fun a => (S a).biUnion R) c).card ≤ e * d := by
  have hsub : inverseScope (fun a => (S a).biUnion R) c ⊆
      (inverseScope R c).biUnion (inverseScope S) := by
    intro a ha
    obtain ⟨b, hb, hc⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp ha).2
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => hS b)).trans
      (Nat.mul_le_mul_right d (hR c)))

theorem overlap_card {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (scope : A → Finset B) (d e : ℕ) (hsize : ∀ a, (scope a).card ≤ d)
    (hinc : ∀ b, (inverseScope scope b).card ≤ e) (a : A) :
    (Finset.univ.filter fun a' => ¬ Disjoint (scope a) (scope a')).card ≤ d * e := by
  have hsub : (Finset.univ.filter fun a' => ¬ Disjoint (scope a) (scope a')) ⊆
      (scope a).biUnion (inverseScope scope) := by
    intro a' ha'
    obtain ⟨b, hb, hb'⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp ha').2
    exact Finset.mem_biUnion.mpr ⟨b, hb,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'⟩⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_biUnion_le_card_mul _ _ _ (fun b _ => hinc b)).trans
      (Nat.mul_le_mul_right e (hsize a)))

private theorem incidence_flip_twice (b : Pos T k) (a : Fin (T.S.n k)) :
    flipPos (flipPos b a) a = b := by
  funext t
  by_cases ht : t = a
  · subst t; simp [flipPos]
  · simp [flipPos, ht]

theorem twoStep_symm {b u : Pos T k} (hu : u ∈ twoStep b) : b ∈ twoStep u := by
  obtain ⟨⟨a, a'⟩, _, rfl⟩ := Finset.mem_image.mp hu
  apply Finset.mem_image.mpr
  refine ⟨(a', a), Finset.mem_univ _, ?_⟩
  simp only [incidence_flip_twice]

theorem ancestors_incidence (m : ℕ) (u : Pos T k) :
    (inverseScope (fun b : Pos T k => ancestors {b} m) u).card ≤
      (1 + T.S.n k ^ 2) ^ m := by
  induction m generalizing u with
  | zero =>
    have heq : inverseScope (fun b : Pos T k => ancestors {b} 0) u = {u} := by
      ext b
      simp only [inverseScope, Finset.mem_filter, Finset.mem_univ, true_and, ancestors, Finset.mem_singleton]
      exact eq_comm
    rw [heq]
    simp
  | succ m ih =>
    have hsub : inverseScope (fun b : Pos T k => ancestors {b} (m + 1)) u ⊆
        inverseScope (fun b : Pos T k => ancestors {b} m) u ∪
          (twoStep u).biUnion (inverseScope (fun b : Pos T k => ancestors {b} m)) := by
      intro b hb
      rcases Finset.mem_union.mp (Finset.mem_filter.mp hb).2 with hu | hu
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
      · obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨v, twoStep_symm huv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩))
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (inverseScope (fun b : Pos T k => ancestors {b} m) u).card +
          ((twoStep u).biUnion (inverseScope (fun b : Pos T k => ancestors {b} m))).card :=
        Finset.card_union_le _ _
      _ ≤ (1 + T.S.n k ^ 2) ^ m + (twoStep u).card * (1 + T.S.n k ^ 2) ^ m :=
        Nat.add_le_add (ih u) (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => ih v))
      _ ≤ (1 + T.S.n k ^ 2) ^ m + T.S.n k ^ 2 * (1 + T.S.n k ^ 2) ^ m :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (twoStep_card u)) _
      _ = _ := by rw [pow_succ]; ring

theorem rowInitialCells_incidence (D : LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (C : D.geom.Cell) :
    (inverseScope (rowInitialCells D) C).card ≤ T.S.n k ^ (κ.Ac + 3) := by
  let flips := fun v : Pos T k => Finset.univ.image (flipPos v)
  have hsub : inverseScope (rowInitialCells D) C ⊆
      (D.encoding.events.incidentEvents C).biUnion flips := by
    intro b hb
    obtain ⟨a, _, hC⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hb).2
    have hv : flipPos b a ∈ D.encoding.events.incidentEvents C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [hD.scope_eq] using hC
    exact Finset.mem_biUnion.mpr ⟨flipPos b a, hv,
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, incidence_flip_twice b a⟩⟩
  have hf : ∀ v, (flips v).card ≤ T.S.n k := by
    intro v
    exact Finset.card_image_le.trans (by simp)
  have hnplus : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (D.encoding.events.incidentEvents C).card * T.S.n k :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hf v)
    _ ≤ (T.S.n k ^ κ.Ac * (T.S.n k + 1)) * T.S.n k :=
      Nat.mul_le_mul_right _ (HypercubeRamsey.Lane_sol_s18_n4.incidentEvents_card_le D hD C)
    _ ≤ (T.S.n k ^ κ.Ac * T.S.n k ^ 2) * T.S.n k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hnplus)
    _ = _ := by ring

theorem ancestorCells_incidence (D : LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (m : ℕ) (C : D.geom.Cell) :
    (inverseScope (fun b : Pos T k => rowCells D (ancestors {b} m)) C).card ≤
      T.S.n k ^ (κ.Ac + 3) * (1 + T.S.n k ^ 2) ^ m :=
  inverse_comp_card (fun b : Pos T k => ancestors {b} m) (rowInitialCells D) _ _
    (ancestors_incidence m) (rowInitialCells_incidence D hD hn) C

theorem graphBall_seed_union (D : LateData hPT) (seed : Finset (Pos T k)) (t : ℕ) :
    D.encoding.events.graphBall seed t =
      seed.biUnion (fun v => D.encoding.events.graphBall {v} t) := by
  induction t with
  | zero => simp [ListEvent.graphBall]
  | succ t ih =>
    ext u
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with hu | hu
      · rw [ih] at hu
        obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu
        exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_union.mpr (Or.inl huv)⟩
      · obtain ⟨_, w, hw, hadj⟩ := Finset.mem_filter.mp hu
        rw [ih] at hw
        obtain ⟨v, hv, hwv⟩ := Finset.mem_biUnion.mp hw
        exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hwv, hadj⟩))⟩
    · intro hu
      obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu
      rcases Finset.mem_union.mp huv with huv | huv
      · exact Finset.mem_union.mpr (Or.inl (ih.symm ▸ Finset.mem_biUnion.mpr ⟨v, hv, huv⟩))
      · obtain ⟨_, w, hw, hadj⟩ := Finset.mem_filter.mp huv
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, w, ih.symm ▸ Finset.mem_biUnion.mpr ⟨v, hv, hw⟩, hadj⟩))

theorem graphBall_incidence (D : LateData hPT) (d : ℕ)
    (hdegree : ∀ v, (Finset.univ.filter fun w => D.encoding.events.Adjacent v w).card ≤ d)
    (t : ℕ) (u : Pos T k) :
    (inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} t) u).card ≤ (d + 1) ^ t := by
  induction t generalizing u with
  | zero =>
    have heq : inverseScope (fun b : Pos T k => D.encoding.events.graphBall {b} 0) u = {u} := by
      ext b
      simp only [inverseScope, Finset.mem_filter, Finset.mem_univ, true_and, ListEvent.graphBall, Finset.mem_singleton]
      exact eq_comm
    rw [heq]
    simp
  | succ t ih =>
    let nbr := Finset.univ.filter fun w => D.encoding.events.Adjacent u w
    have hsub : inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} (t + 1)) u ⊆
        inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} t) u ∪
          nbr.biUnion (inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} t)) := by
      intro v hv
      rcases Finset.mem_union.mp (Finset.mem_filter.mp hv).2 with hu | hu
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩))
      · obtain ⟨_, w, hw, hadj⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
          ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩))
    calc
      _ ≤ _ := Finset.card_le_card hsub
      _ ≤ (inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} t) u).card +
          (nbr.biUnion (inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} t))).card :=
        Finset.card_union_le _ _
      _ ≤ (d + 1) ^ t + nbr.card * (d + 1) ^ t :=
        Nat.add_le_add (ih u) (Finset.card_biUnion_le_card_mul _ _ _ (fun w _ => ih w))
      _ ≤ (d + 1) ^ t + d * (d + 1) ^ t :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (hdegree u)) _
      _ = _ := by rw [pow_succ]; ring

theorem expandCells_incidence (D : LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (C : D.geom.Cell) :
    (inverseScope (fun C' => D.expandCells {C'}) C).card ≤
      1 + (T.S.n k ^ κ.Ac * (T.S.n k + 1)) *
        (T.S.n k ^ (κ.Ac + 4) + 1) ^ (2 * D.encoding.Ts + 3) * (T.S.n k + 1) := by
  let d := T.S.n k ^ (κ.Ac + 4)
  let t := 2 * D.encoding.Ts + 3
  let roots := D.encoding.events.incidentEvents C
  let prev := roots.biUnion (inverseScope (fun v : Pos T k => D.encoding.events.graphBall {v} t))
  have hsub : inverseScope (fun C' => D.expandCells {C'}) C ⊆ {C} ∪ prev.biUnion D.encoding.events.scope := by
    intro C' hC'
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hC').2 with heq | hscope
    · exact Finset.mem_union.mpr (Or.inl (by simpa only [Finset.mem_singleton] using
        (Finset.mem_singleton.mp heq).symm))
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hscope
      have hvroot : v ∈ roots := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCv⟩
      have hv' : v ∈ D.encoding.events.graphBall (D.encoding.events.incidentEvents C') t := by
        simpa only [Finset.singleton_biUnion] using hv
      rw [graphBall_seed_union] at hv'
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv'
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_biUnion.mpr ⟨v, hvroot,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw⟩⟩, (Finset.mem_filter.mp hw).2⟩))
  have hprev : prev.card ≤ (T.S.n k ^ κ.Ac * (T.S.n k + 1)) * (d + 1) ^ t := by
    exact (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => graphBall_incidence D d
      (HypercubeRamsey.Lane_sol_s18_n4.eventDegreeBound D hD hn) t v)).trans
        (Nat.mul_le_mul_right _ (HypercubeRamsey.Lane_sol_s18_n4.incidentEvents_card_le D hD C))
  have hscopes : ∀ v, (D.encoding.events.scope v).card ≤ T.S.n k + 1 := by
    intro v
    exact HypercubeRamsey.Lane_sol_s18_n4.eventScope_card_le D hD v
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ 1 + (prev.biUnion D.encoding.events.scope).card := by
      simpa only [Finset.card_singleton] using Finset.card_union_le {C} _
    _ ≤ 1 + prev.card * (T.S.n k + 1) :=
      Nat.add_le_add_left (Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => hscopes v)) _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ hprev) _

theorem expandCells_seed_union (D : LateData hPT) (seed : Finset D.geom.Cell) :
    D.expandCells seed = seed.biUnion (fun C => D.expandCells {C}) := by
  ext C
  constructor
  · intro hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_union.mpr
        (Or.inl (Finset.mem_singleton_self _))⟩
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
      rw [graphBall_seed_union] at hv
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨C', hC', hwC'⟩ := Finset.mem_biUnion.mp hw
      have hv' : v ∈ D.encoding.events.graphBall (D.encoding.events.incidentEvents C')
          (2 * D.encoding.Ts + 3) := by
        rw [graphBall_seed_union]
        exact Finset.mem_biUnion.mpr ⟨w, hwC', hvw⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨C', hC', Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨v, ?_, hCv⟩))⟩
      simpa only [Finset.singleton_biUnion] using hv'
  · intro hC
    obtain ⟨C', hC', hCC'⟩ := Finset.mem_biUnion.mp hC
    rcases Finset.mem_union.mp hCC' with heq | hv
    · exact Finset.mem_union.mpr (Or.inl ((Finset.mem_singleton.mp heq) ▸ hC'))
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hv
      have hv' : v ∈ D.encoding.events.graphBall (D.encoding.events.incidentEvents C')
          (2 * D.encoding.Ts + 3) := by
        simpa only [Finset.singleton_biUnion] using hv
      rw [graphBall_seed_union] at hv'
      obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv'
      apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_biUnion.mpr
      refine ⟨v, ?_, hCv⟩
      rw [graphBall_seed_union]
      exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_biUnion.mpr ⟨C', hC', hw⟩, hvw⟩

private theorem growth_power {n a t : ℕ} (hn : 2 ≤ n) :
    1 + (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1) ≤
      n ^ ((a + 5) * (2 * t + 4) + 3) := by
  have hp : 0 < n ^ (a + 4) := pow_pos (by omega) _
  have hd : n ^ (a + 4) + 1 ≤ n ^ (a + 5) := by
    calc
      _ ≤ n ^ (a + 4) * n := by nlinarith
      _ = _ := (pow_succ n (a + 4)).symm
  have hnplus : n + 1 ≤ n ^ 2 := by nlinarith
  let z := (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1)
  have hz : 1 ≤ z := by
    dsimp [z]
    have hp := pow_pos (by omega : 0 < n ^ (a + 4) + 1) (2 * t + 4)
    nlinarith
  calc
    1 + z ≤ n * z := by nlinarith
    _ ≤ n * ((n ^ (a + 5)) ^ (2 * t + 4) * n ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hnplus)
    _ = _ := by rw [← pow_mul]; ring

theorem horizon_incidence_power (D : LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (m : ℕ) (C : D.geom.Cell) :
    (inverseScope (fun b : Pos T k => D.expandCells (rowCells D (ancestors {b} m))) C).card ≤
      T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3 + (κ.Ac + 3) + 3 * m) := by
  let grow := (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3
  have hd : 1 + T.S.n k ^ 2 ≤ T.S.n k ^ 3 := by nlinarith
  have hinc : ∀ C, (inverseScope (fun C' => D.expandCells {C'}) C).card ≤ T.S.n k ^ grow := by
    intro C
    have hI := expandCells_incidence D hD hn C
    have hbase : T.S.n k ^ κ.Ac * (T.S.n k + 1) ≤ T.S.n k ^ (κ.Ac + 4) + 1 := by
      have hnp : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
      have hex : κ.Ac + 2 ≤ κ.Ac + 4 := by omega
      calc
        _ ≤ T.S.n k ^ κ.Ac * T.S.n k ^ 2 := Nat.mul_le_mul_left _ hnp
        _ = T.S.n k ^ (κ.Ac + 2) := (pow_add _ _ _).symm
        _ ≤ T.S.n k ^ (κ.Ac + 4) := Nat.pow_le_pow_right (by omega) hex
        _ ≤ _ := Nat.le_add_right _ _
    apply hI.trans
    apply le_trans _ (growth_power hn)
    have hh := Nat.mul_le_mul_right ((T.S.n k ^ (κ.Ac + 4) + 1) ^ (2 * D.encoding.Ts + 3)) hbase
    have hh' := Nat.mul_le_mul_right (T.S.n k + 1) hh
    conv_rhs => rw [show 2 * D.encoding.Ts + 4 = (2 * D.encoding.Ts + 3) + 1 by omega, pow_succ]
    simpa only [mul_comm, mul_left_comm, mul_assoc] using Nat.add_le_add_left hh' 1
  have hrows : ∀ C, (inverseScope (fun b : Pos T k => rowCells D (ancestors {b} m)) C).card ≤
      T.S.n k ^ (κ.Ac + 3 + 3 * m) := by
    intro C
    apply (ancestorCells_incidence D hD hn m C).trans
    calc
      _ ≤ T.S.n k ^ (κ.Ac + 3) * (T.S.n k ^ 3) ^ m :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd m)
      _ = _ := by rw [← pow_mul, ← pow_add]
  have h := inverse_comp_card (fun b : Pos T k => rowCells D (ancestors {b} m))
    (fun C => D.expandCells {C}) _ _ hrows hinc C
  simp_rw [← expandCells_seed_union] at h
  simpa only [← pow_add, grow, Nat.add_assoc] using h




end HypercubeRamsey.S18.Lane_sol_s18_n5
