import HypercubeRamsey.S17.Nodes_sol_s17_res
import HypercubeRamsey.S17.Execution_sol_s17_res

namespace HypercubeRamsey.Lane_sol_s17_res

open Classical

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
variable {D : ListGateContext κ T k PT}

private noncomputable def priority (order : Pos T k → ℕ) (v : Pos T k) : ℕ :=
  order v * Fintype.card (Pos T k) + ListEvent.canonicalRank v

private theorem before_priority_lt (order : Pos T k → ℕ) {v w : Pos T k}
    (h : ListEvent.before order v w) : priority order v < priority order w := by
  have hv : ListEvent.canonicalRank v < Fintype.card (Pos T k) :=
    (Fintype.equivFin (Pos T k) v).isLt
  have hw : ListEvent.canonicalRank w < Fintype.card (Pos T k) :=
    (Fintype.equivFin (Pos T k) w).isLt
  rcases h with h | ⟨h, hh⟩
  · have hp := Nat.mul_le_mul_right (Fintype.card (Pos T k)) (Nat.succ_le_of_lt h)
    dsimp [priority]
    nlinarith
  · dsimp [priority]
    rw [h]
    omega

noncomputable def everTrue (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C) : Finset (Pos T k) :=
  events.filter fun w => ∃ n, n ≤ Ts ∧ LE.S w (LE.runRounds n order events pools tapes).1

noncomputable def trueComponent (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) : Finset (Pos T k) :=
  let E := everTrue LE Ts order events pools tapes
  E.filter fun w => Relation.ReflTransGen (fun a b => a ∈ E ∧ b ∈ E ∧ LE.Adjacent a b) root w

theorem component_root (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) (hroot : root ∈ events)
    (hfinal : LE.S root (LE.resample Ts order events pools tapes)) :
    root ∈ trueComponent LE Ts order events pools tapes root := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨hroot, Ts, le_rfl, hfinal⟩, Relation.ReflTransGen.refl⟩

theorem component_closed (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) {v w : Pos T k}
    (hv : v ∈ trueComponent LE Ts order events pools tapes root)
    (hw : w ∈ everTrue LE Ts order events pools tapes)
    (hmeet : ¬ Disjoint (LE.scope v) (LE.scope w)) :
    w ∈ trueComponent LE Ts order events pools tapes root := by
  by_cases he : v = w
  · exact he ▸ hv
  · obtain ⟨hvE, hpath⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hw, hpath.tail ⟨hvE, hw, he, hmeet⟩⟩

theorem component_active_closed (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) {n : ℕ} (hn : n < Ts) {v w : Pos T k}
    (hv : v ∈ trueComponent LE Ts order events pools tapes root)
    (hw : w ∈ LE.active order events (LE.runRounds n order events pools tapes).1)
    (hmeet : ¬ Disjoint (LE.scope v) (LE.scope w)) :
    w ∈ trueComponent LE Ts order events pools tapes root := by
  have hw' := (Finset.mem_filter.mp hw).2
  exact component_closed LE Ts order events pools tapes root hv
    (Finset.mem_filter.mpr ⟨hw'.1, n, by omega, hw'.2.1⟩) hmeet

theorem component_true_each_round (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) (hroot : root ∈ events)
    (hfinal : LE.S root (LE.resample Ts order events pools tapes)) :
    ∀ n, n ≤ Ts → ∃ v ∈ trueComponent LE Ts order events pools tapes root,
      LE.S v (LE.runRounds n order events pools tapes).1 := by
  let comp := trueComponent LE Ts order events pools tapes root
  have step (n : ℕ) (hn : n < Ts)
      (h : ∃ v ∈ comp, LE.S v (LE.runRounds (n + 1) order events pools tapes).1) :
      ∃ v ∈ comp, LE.S v (LE.runRounds n order events pools tapes).1 := by
    obtain ⟨v, hv, htrue⟩ := h
    by_cases ht : ∃ C ∈ LE.scope v, ∃ w ∈ LE.active order events
        (LE.runRounds n order events pools tapes).1, C ∈ LE.scope w
    · obtain ⟨C, hCv, w, hw, hCw⟩ := ht
      exact ⟨w, component_active_closed LE Ts order events pools tapes root hn hv hw
        (fun h => Finset.disjoint_left.mp h hCv hCw),
        (Finset.mem_filter.mp hw).2.2.1⟩
    · refine ⟨v, hv, (LE.scope_ok v _ _ ?_).mp htrue⟩
      intro C hC
      have hno : ¬ ∃ w ∈ LE.active order events
          (LE.runRounds n order events pools tapes).1, C ∈ LE.scope w := by
        intro h
        exact ht ⟨C, hC, h⟩
      rw [show LE.runRounds (n + 1) order events pools tapes =
        LE.round order events pools tapes (LE.runRounds n order events pools tapes).1
          (LE.runRounds n order events pools tapes).2 by rfl]
      simp [ListEvent.round, hno]
  have backward : ∀ q, q ≤ Ts → ∃ v ∈ comp,
      LE.S v (LE.runRounds (Ts - q) order events pools tapes).1 := by
    intro q
    induction q with
    | zero =>
      intro h
      exact ⟨root, component_root LE Ts order events pools tapes root hroot hfinal, hfinal⟩
    | succ q ih =>
      intro hq
      have hp := ih (by omega)
      have he : Ts - q = (Ts - (q + 1)) + 1 := by omega
      rw [he] at hp
      exact step (Ts - (q + 1)) (by omega) hp
  intro n hn
  have h := backward (Ts - n) (by omega)
  simpa only [Nat.sub_sub_self hn] using h

theorem component_execution_each_round (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) (hroot : root ∈ events)
    (hfinal : LE.S root (LE.resample Ts order events pools tapes))
    (n : ℕ) (hn : n < Ts) :
    ∃ v ∈ trueComponent LE Ts order events pools tapes root,
      v ∈ LE.active order events (LE.runRounds n order events pools tapes).1 := by
  let comp := trueComponent LE Ts order events pools tapes root
  let trueSites := comp.filter fun v => LE.S v (LE.runRounds n order events pools tapes).1
  have hne : trueSites.Nonempty := by
    obtain ⟨v, hv, htrue⟩ := component_true_each_round LE Ts order events pools tapes root
      hroot hfinal n (by omega)
    exact ⟨v, Finset.mem_filter.mpr ⟨hv, htrue⟩⟩
  obtain ⟨v, hv, hmin⟩ := Finset.exists_min_image trueSites (priority order) hne
  obtain ⟨hvcomp, hvtrue⟩ := Finset.mem_filter.mp hv
  refine ⟨v, hvcomp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hvtrue, ?_⟩⟩
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hvcomp).1).1
  · intro w hw hbefore hadj htrue
    have hwcomp : w ∈ comp := component_closed LE Ts order events pools tapes root hvcomp
      (Finset.mem_filter.mpr ⟨hw, n, by omega, htrue⟩)
      (fun h => hadj.2 h.symm)
    have hh := hmin w (Finset.mem_filter.mpr ⟨hwcomp, htrue⟩)
    have hlt := before_priority_lt order hbefore
    omega

private theorem ball_mono (LE : ListEvent D.F) (seed : Finset (Pos T k))
    {n m : ℕ} (h : n ≤ m) : LE.graphBall seed n ⊆ LE.graphBall seed m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction a with
  | zero => exact Finset.Subset.refl _
  | succ a ih => exact ih.trans (Finset.subset_union_left)

private theorem ball_step (LE : ListEvent D.F) (seed : Finset (Pos T k))
    {n : ℕ} {v w : Pos T k} (hv : v ∈ LE.graphBall seed n)
    (h : LE.Adjacent w v) : w ∈ LE.graphBall seed (n + 1) := by
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, h⟩)

private theorem adjacent_symm (LE : ListEvent D.F) {v w : Pos T k}
    (h : LE.Adjacent v w) : LE.Adjacent w v :=
  ⟨Ne.symm h.1, fun hd => h.2 hd.symm⟩

private theorem ball_one_cases (LE : ListEvent D.F) {v w : Pos T k}
    (h : v ∈ LE.graphBall {w} 1) : v = w ∨ LE.Adjacent v w := by
  simpa [ListEvent.graphBall] using h

private theorem ball_one_symm (LE : ListEvent D.F) {v w : Pos T k}
    (h : v ∈ LE.graphBall {w} 1) : w ∈ LE.graphBall {v} 1 := by
  rcases ball_one_cases LE h with rfl | h
  · simp [ListEvent.graphBall]
  · exact ball_step LE {v} (n := 0) (v := v) (w := w)
      (by simp [ListEvent.graphBall]) (adjacent_symm LE h)

private theorem ball_one_meet (LE : ListEvent D.F) {v w : Pos T k}
    (h : ¬ Disjoint (LE.scope v) (LE.scope w)) : v ∈ LE.graphBall {w} 1 := by
  by_cases he : v = w
  · subst v; simp [ListEvent.graphBall]
  · exact ball_step LE {w} (n := 0) (by simp [ListEvent.graphBall]) ⟨he, h⟩

private theorem ball_three_between (LE : ListEvent D.F) {a b v w : Pos T k}
    (ha : a ∈ LE.graphBall {v} 1) (hb : b ∈ LE.graphBall {w} 1)
    (hvw : v = w ∨ LE.Adjacent w v) : b ∈ LE.graphBall {a} 3 := by
  have hv := ball_one_symm LE ha
  have hw : w ∈ LE.graphBall {a} 2 := by
    rcases hvw with rfl | h
    · exact ball_mono LE _ (by omega) hv
    · exact ball_step LE _ hv h
  rcases ball_one_cases LE hb with rfl | h
  · exact ball_mono LE _ (by omega) hw
  · exact ball_step LE _ hw h

private theorem independent_cover {α : Type*} [DecidableEq α]
    (scope : α → Finset D.G.Cell) (s : Finset α) :
    ∃ J : Finset α, J ⊆ s ∧
      (∀ a ∈ J, ∀ b ∈ J, a ≠ b → Disjoint (scope a) (scope b)) ∧
      ∀ a ∈ s, a ∈ J ∨ ∃ b ∈ J, ¬ Disjoint (scope a) (scope b) := by
  classical
  let P : Finset α → Prop := fun J =>
    ∀ a ∈ J, ∀ b ∈ J, a ≠ b → Disjoint (scope a) (scope b)
  let choices := s.powerset.filter P
  have hne : choices.Nonempty := ⟨∅, by
    apply Finset.mem_filter.mpr
    exact ⟨by simp, by intro a ha; simpa using ha⟩⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image choices Finset.card hne
  obtain ⟨hJs, hind⟩ := Finset.mem_filter.mp hJ
  have hsub : J ⊆ s := Finset.mem_powerset.mp hJs
  refine ⟨J, hsub, hind, ?_⟩
  intro a ha
  by_cases h : a ∈ J
  · exact Or.inl h
  · right
    by_contra hn
    have hd : ∀ b ∈ J, Disjoint (scope a) (scope b) := by
      intro b hb
      by_contra hh
      exact hn ⟨b, hb, hh⟩
    have hnew : insert a J ∈ choices := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha hsub), ?_⟩
      intro x hx y hy hxy
      by_cases hxa : x = a
      · subst x
        by_cases hya : y = a
        · subst y; exact (hxy rfl).elim
        · exact hd y ((Finset.mem_insert.mp hy).resolve_left hya)
      · have hxJ : x ∈ J := (Finset.mem_insert.mp hx).resolve_left hxa
        by_cases hya : y = a
        · subst y; exact (hd x hxJ).symm
        · exact hind x hxJ y ((Finset.mem_insert.mp hy).resolve_left hya) hxy
    have hh := hmax (insert a J) hnew
    rw [Finset.card_insert_of_notMem h] at hh
    omega

theorem component_connected (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k)
    (hr : root ∈ trueComponent LE Ts order events pools tapes root)
    {v : Pos T k} (hv : v ∈ trueComponent LE Ts order events pools tapes root) :
    Relation.ReflTransGen (fun a b => a ∈ trueComponent LE Ts order events pools tapes root ∧
      b ∈ trueComponent LE Ts order events pools tapes root ∧ LE.Adjacent a b) root v := by
  obtain ⟨hvE, hpath⟩ := Finset.mem_filter.mp hv
  have aux : ∀ v, Relation.ReflTransGen
      (fun a b => a ∈ everTrue LE Ts order events pools tapes ∧
        b ∈ everTrue LE Ts order events pools tapes ∧ LE.Adjacent a b) root v →
      v ∈ trueComponent LE Ts order events pools tapes root ∧
      Relation.ReflTransGen (fun a b => a ∈ trueComponent LE Ts order events pools tapes root ∧
        b ∈ trueComponent LE Ts order events pools tapes root ∧ LE.Adjacent a b) root v := by
    intro v h
    induction h with
    | refl => exact ⟨hr, Relation.ReflTransGen.refl⟩
    | @tail a b hab he ih =>
      have hb := component_closed LE Ts order events pools tapes root ih.1 he.2.1 he.2.2.2
      exact ⟨hb, ih.2.tail ⟨ih.1, hb, he.2.2⟩⟩
  exact (aux v hpath).2

private theorem dominating_tree
    {ι : Type*} [DecidableEq ι] (LE : ListEvent D.F)
    (comp : Finset (Pos T k)) (root : Pos T k) (hroot : root ∈ comp)
    (hconn : ∀ v ∈ comp, Relation.ReflTransGen
      (fun a b => a ∈ comp ∧ b ∈ comp ∧ LE.Adjacent a b) root v)
    (I : Finset ι) (site : ι → Pos T k) (hsite : ∀ i ∈ I, site i ∈ comp)
    (hcover : ∀ v ∈ comp, ∃ i ∈ I, site i ∈ LE.graphBall {v} 1) :
    ∃ m, ∃ hm : 0 < m, ∃ Q : TreeCode m, ∃ f : Fin m → ι,
      TreeSpec Q ∧ Function.Injective f ∧ Finset.univ.image f = I ∧
      site (f ⟨0, hm⟩) ∈ LE.graphBall {root} 1 ∧
      ∀ j, 0 < j.val → site (f j) ∈ LE.graphBall {site (f (Q.2 j))} 3 := by
  let repr (v : {v : Pos T k // v ∈ comp}) : ι := Classical.choose (hcover v.1 v.2)
  have hrepr (v : {v : Pos T k // v ∈ comp}) :
      repr v ∈ I ∧ site (repr v) ∈ LE.graphBall {v.1} 1 :=
    Classical.choose_spec (hcover v.1 v.2)
  let anchor := repr ⟨root, hroot⟩
  let R := fun a b : ι => site b ∈ LE.graphBall {site a} 3
  have hpaths : ∀ v (hv : v ∈ comp), Relation.ReflTransGen
      (fun a b => a ∈ I ∧ b ∈ I ∧ R a b) anchor (repr ⟨v, hv⟩) := by
    intro v hv
    have hp := hconn v hv
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab he ih =>
      have hh := ball_three_between LE (hrepr ⟨a, he.1⟩).2 (hrepr ⟨b, he.2.1⟩).2
        (Or.inr (adjacent_symm LE he.2.2))
      exact (ih he.1).tail ⟨(hrepr ⟨a, he.1⟩).1, (hrepr ⟨b, he.2.1⟩).1, hh⟩
  have hI : ∀ i ∈ I, Relation.ReflTransGen
      (fun a b => a ∈ I ∧ b ∈ I ∧ R a b) anchor i := by
    intro i hi
    have hv := hsite i hi
    have hh := ball_three_between LE (hrepr ⟨site i, hv⟩).2
      (show site i ∈ LE.graphBall {site i} 1 by simp [ListEvent.graphBall]) (Or.inl rfl)
    exact (hpaths (site i) hv).tail ⟨(hrepr ⟨site i, hv⟩).1, hi, hh⟩
  obtain ⟨m, hm, Q, f, hQ, hf, hcov, hr, he⟩ :=
    spanning_preorder R anchor I (hrepr ⟨root, hroot⟩).1 hI
  exact ⟨m, hm, Q, f, hQ, hf, hcov, hr ▸ (hrepr ⟨root, hroot⟩).2, he⟩

structure ComponentData (LE : ListEvent D.F) (Ts : ℕ) (order : Pos T k → ℕ)
    (events : Finset (Pos T k)) (pools : ∀ C, D.F.Pool C)
    (tapes : ∀ C, ℕ → TapeEntry D.F C) (root : Pos T k) (m : ℕ) where
  rounds_le : Ts ≤ m
  positive : 0 < m
  Q : TreeCode m
  items : Fin m → Pos T k × Option (Fin Ts)
  tree : TreeSpec Q
  injective : Function.Injective items
  anchor : (items ⟨0, positive⟩).1 ∈ LE.graphBall {root} 1
  events_mem : ∀ j, (items j).1 ∈ events
  child : ∀ j, 0 < j.val → (items j).1 ∈ LE.graphBall {(items (Q.2 j)).1} 3
  real_exec : ∀ j r, (items j).2 = some r →
    Executed LE order events pools tapes ((items j).1, r)
  prior_closed : ∀ j r, (items j).2 = some r → ∀ C ∈ LE.scope (items j).1,
    ∀ o : Pos T k × Fin Ts, Executed LE order events pools tapes o →
      o.2.val < r.val → C ∈ LE.scope o.1 → ∃ i, items i = (o.1, some o.2)
  extra_truth : ∀ j, (items j).2 = none →
    ∃ n, n ≤ Ts ∧ LE.S (items j).1 (LE.runRounds n order events pools tapes).1
  extra_untouched : ∀ j, (items j).2 = none → ∀ C ∈ LE.scope (items j).1,
    ∀ n, n < Ts → ¬ ∃ v ∈ LE.active order events
      (LE.runRounds n order events pools tapes).1, C ∈ LE.scope v
  extra_disjoint : ∀ i j, i ≠ j → (items i).2 = none → (items j).2 = none →
    Disjoint (LE.scope (items i).1) (LE.scope (items j).1)

theorem component_data (LE : ListEvent D.F) (Ts : ℕ)
    (order : Pos T k → ℕ) (events : Finset (Pos T k))
    (pools : ∀ C, D.F.Pool C) (tapes : ∀ C, ℕ → TapeEntry D.F C)
    (root : Pos T k) (hroot : root ∈ events)
    (hfinal : LE.S root (LE.resample Ts order events pools tapes)) :
    ∃ m, Nonempty (ComponentData LE Ts order events pools tapes root m) := by
  let comp := trueComponent LE Ts order events pools tapes root
  let E : Finset (Pos T k × Fin Ts) := Finset.univ.filter fun o =>
    Executed LE order events pools tapes o ∧ o.1 ∈ comp
  let typed : Pos T k × Fin Ts → Pos T k × Option (Fin Ts) := fun o => (o.1, some o.2)
  let extra : Pos T k → Pos T k × Option (Fin Ts) := fun v => (v, none)
  let residue := comp.filter fun v => ∀ o ∈ E, v ∉ LE.graphBall {o.1} 1
  obtain ⟨J, hJsub, hJdis, hJcover⟩ := independent_cover LE.scope residue
  let I := E.image typed ∪ J.image extra
  have hrootcomp : root ∈ comp := component_root LE Ts order events pools tapes root hroot hfinal
  have hEtyped {o : Pos T k × Fin Ts} (ho : o ∈ E) : typed o ∈ I :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨o, ho, rfl⟩)
  have hJextra {v : Pos T k} (hv : v ∈ J) : extra v ∈ I :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
  have hsites : ∀ i ∈ I, i.1 ∈ comp := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp ho).2.2
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp (hJsub hv)).1
  have hcover : ∀ v ∈ comp, ∃ i ∈ I, i.1 ∈ LE.graphBall {v} 1 := by
    intro v hv
    by_cases hr : v ∈ residue
    · rcases hJcover v hr with hj | ⟨w, hw, hmeet⟩
      · exact ⟨extra v, hJextra hj, by simp [extra, ListEvent.graphBall]⟩
      · exact ⟨extra w, hJextra hw, ball_one_symm LE (ball_one_meet LE hmeet)⟩
    · have hh : ¬ ∀ o ∈ E, v ∉ LE.graphBall {o.1} 1 := by
        intro h
        exact hr (Finset.mem_filter.mpr ⟨hv, h⟩)
      push Not at hh
      obtain ⟨o, ho, hnear⟩ := hh
      exact ⟨typed o, hEtyped ho, ball_one_symm LE hnear⟩
  obtain ⟨m, hm, Q, items, hQ, hinj, hcov, hanchor, hchild⟩ := dominating_tree LE comp root
    hrootcomp (fun v hv => component_connected LE Ts order events pools tapes root hrootcomp hv)
    I Prod.fst hsites hcover
  have hMem (j : Fin m) : items j ∈ I := by
    rw [← hcov]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hReal (j : Fin m) (r : Fin Ts) (hr : (items j).2 = some r) :
      ((items j).1, r) ∈ E := by
    rcases Finset.mem_union.mp (hMem j) with h | h
    · obtain ⟨o, ho, he⟩ := Finset.mem_image.mp h
      have hsite : o.1 = (items j).1 := congrArg Prod.fst he
      have hround : o.2 = r := Option.some.inj ((congrArg Prod.snd he).trans hr)
      have heq : o = ((items j).1, r) := Prod.ext hsite hround
      exact heq ▸ ho
    · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
      have hh := (congrArg Prod.snd he).trans hr
      contradiction
  have hExtra (j : Fin m) (hr : (items j).2 = none) : (items j).1 ∈ J := by
    rcases Finset.mem_union.mp (hMem j) with h | h
    · obtain ⟨o, ho, he⟩ := Finset.mem_image.mp h
      have hh := (congrArg Prod.snd he).trans hr
      contradiction
    · obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
      have hsite : v = (items j).1 := congrArg Prod.fst he
      exact hsite ▸ hv
  have hround : ∀ r : Fin Ts, ∃ j, (items j).2 = some r := by
    intro r
    obtain ⟨v, hv, hexec⟩ := component_execution_each_round LE Ts order events pools tapes root
      hroot hfinal r.val r.isLt
    have ho : (v, r) ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexec, hv⟩
    have hI := hEtyped ho
    rw [← hcov] at hI
    obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hI
    exact ⟨j, congrArg Prod.snd he⟩
  let index (r : Fin Ts) : Fin m := Classical.choose (hround r)
  have hindex (r : Fin Ts) : (items (index r)).2 = some r := Classical.choose_spec (hround r)
  have hindexinj : Function.Injective index := by
    intro r s he
    apply Option.some.inj
    exact (hindex r).symm.trans ((congrArg (fun j => (items j).2) he).trans (hindex s))
  have hsize : Ts ≤ m := by simpa using Fintype.card_le_of_injective index hindexinj
  refine ⟨m, ⟨{
    rounds_le := hsize
    positive := hm
    Q := Q
    items := items
    tree := hQ
    injective := hinj
    anchor := hanchor
    events_mem := ?_
    child := hchild
    real_exec := ?_
    prior_closed := ?_
    extra_truth := ?_
    extra_untouched := ?_
    extra_disjoint := ?_ }⟩⟩
  · intro j
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hsites _ (hMem j))).1).1
  · intro j r hr
    exact (Finset.mem_filter.mp (hReal j r hr)).2.1
  · intro j r hr C hC o he ho hCo
    have hoComp := component_active_closed LE Ts order events pools tapes root o.2.isLt
      (hsites _ (hMem j)) he (fun hd => Finset.disjoint_left.mp hd hC hCo)
    have hoE : o ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hoComp⟩
    have hoI := hEtyped hoE
    rw [← hcov] at hoI
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hoI
    exact ⟨i, heq⟩
  · intro j hj
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hsites _ (hMem j))).1).2
  · intro j hj C hC n hn htouch
    obtain ⟨v, hv, hCv⟩ := htouch
    have hvComp := component_active_closed LE Ts order events pools tapes root hn
      (hsites _ (hMem j)) hv (fun hd => Finset.disjoint_left.mp hd hC hCv)
    have hvE : (v, (⟨n, hn⟩ : Fin Ts)) ∈ E :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hvComp⟩
    have hres := (Finset.mem_filter.mp (hJsub (hExtra j hj))).2
    exact hres (v, ⟨n, hn⟩) hvE (ball_one_meet LE
      (fun hd => Finset.disjoint_left.mp hd hC hCv))
  · intro i j hij hi hj
    apply hJdis _ (hExtra i hi) _ (hExtra j hj)
    intro he
    apply hij
    apply hinj
    exact Prod.ext he (hi.trans hj.symm)

end HypercubeRamsey.Lane_sol_s17_res
