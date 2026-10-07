import HypercubeRamsey.S18.Nodes_sol_s18_n5
import HypercubeRamsey.S18.Leaf_sol_s18_n4
import HypercubeRamsey.S18.Locality_sol_s18_n4

namespace HypercubeRamsey.Lane_sol_s18_3e
open Classical
open scoped BigOperators

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid}

noncomputable def requirementRegion (D : S18.LateData hPT) :
    S18.TerminalIndex D → Finset D.geom.Cell
  | .inl (.inl C) => {C}
  | .inl (.inr v) => D.encoding.events.scope v
  | .inr (.inl v) => D.initialRegion v
  | .inr (.inr F) => D.lateRegion F

/-- The three initial requirements have their concrete deterministic scopes.
Only the late-risk probability needs a reference-run locality input. -/
theorem terminalFailure_local (D : S18.LateData hPT) (δ : ℝ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (f : S18.TerminalIndex D) (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ requirementRegion D f, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    S18.terminalFailure D δ f x ↔ S18.terminalFailure D δ f x' := by
  cases f with
  | inl f =>
    cases f with
    | inl C =>
      have hp := (hx C (by simp [requirementRegion])).1
      simp only [S18.terminalFailure, hp]
    | inr v =>
      exact not_congr (S18.Lane_sol_s18_n5.poolListOK_local D v x.1 x'.1
        (fun C hC => (hx C hC).1))
  | inr f =>
    cases f with
    | inl v =>
      have hgate := S18.Lane_sol_s18_n5.poolGate_local D (D.initialRegion v)
        x x' (fun C hC => (hx C hC).1)
      have hstate := S18.Lane_sol_s18_n5.initialState_local D
        (D.encoding.events.scope v) x x' hx
      exact and_congr hgate (D.encoding.events.scope_ok v _ _ hstate)
    | inr F =>
      have hgate := S18.Lane_sol_s18_n5.poolGate_local D (D.lateRegion F)
        x x' (fun C hC => (hx C hC).1)
      simp only [S18.terminalFailure, hgate, hlate F x x' hx]

abbrev PoolSlice (D : S18.LateData hPT) (f : S18.TerminalIndex D) :=
  ∀ C : {C : D.geom.Cell // C ∈ requirementRegion D f}, D.fresh.Pool C.1

abbrev LeafKey (D : S18.LateData hPT) := Σ f : S18.TerminalIndex D, PoolSlice D f

noncomputable instance (D : S18.LateData hPT) : Fintype (LeafKey D) := inferInstance

def restrictPools (D : S18.LateData hPT) (f : S18.TerminalIndex D)
    (x : D.encoding.InitInput) : PoolSlice D f := fun C => x.1 C.1

noncomputable def leaf (D : S18.LateData hPT) (δ : ℝ) (L : LeafKey D) :
    Finset D.encoding.InitInput :=
  Finset.univ.filter fun x => restrictPools D L.1 x = L.2 ∧ S18.terminalFailure D δ L.1 x

theorem mem_leaf (D : S18.LateData hPT) (δ : ℝ) (L : LeafKey D)
    (x : D.encoding.InitInput) :
    x ∈ leaf D δ L ↔ restrictPools D L.1 x = L.2 ∧ S18.terminalFailure D δ L.1 x := by
  simp [leaf]

theorem leaf_covers (D : S18.LateData hPT) (δ : ℝ) (f : S18.TerminalIndex D)
    (x : D.encoding.InitInput) :
    S18.terminalFailure D δ f x ↔ ∃ L : LeafKey D, L.1 = f ∧ x ∈ leaf D δ L := by
  constructor
  · intro hx
    exact ⟨⟨f, restrictPools D f x⟩, rfl, (mem_leaf D δ _ x).2 ⟨rfl, hx⟩⟩
  · rintro ⟨⟨f', p⟩, rfl, hx⟩
    exact ((mem_leaf D δ _ x).1 hx).2

abbrev RegionSlot (D : S18.LateData hPT) (f : S18.TerminalIndex D) :=
  Σ C : {C : D.geom.Cell // C ∈ requirementRegion D f}, Fin (D.geom.nslot C.1)

noncomputable def domains (D : S18.LateData hPT) (f : S18.TerminalIndex D) :
    Finset (Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)) :=
  Finset.univ.image fun s : RegionSlot D f => (⟨s.1.1, s.2⟩ : Sigma fun C => Fin (D.geom.nslot C))

noncomputable def images (D : S18.LateData hPT) (L : LeafKey D) :
    Finset (Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :=
  Finset.univ.image fun s : RegionSlot D L.1 => ⟨D.geom.cellPatch s.1.1, L.2 s.1 s.2⟩

theorem mem_domains (D : S18.LateData hPT) (f : S18.TerminalIndex D)
    (s : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)) :
    s ∈ domains D f ↔ s.1 ∈ requirementRegion D f := by
  constructor
  · intro hs
    obtain ⟨t, _, heq⟩ := Finset.mem_image.mp hs
    exact heq ▸ t.1.2
  · intro hs
    exact Finset.mem_image.mpr ⟨⟨⟨s.1, hs⟩, s.2⟩, Finset.mem_univ _, rfl⟩

theorem domains_card (D : S18.LateData hPT) (f : S18.TerminalIndex D) :
    (domains D f).card = Fintype.card (RegionSlot D f) := by
  rw [domains, Finset.card_image_of_injective, Finset.card_univ]
  intro a b heq
  cases a with
  | mk a s =>
    cases b with
    | mk b t =>
      have hab : a = b := Subtype.ext (congrArg Sigma.fst heq)
      cases hab
      have hst : s = t := eq_of_heq (Sigma.mk.inj heq).2
      cases hst
      rfl

theorem images_card_le (D : S18.LateData hPT) (L : LeafKey D) :
    (images D L).card ≤ (domains D L.1).card := by
  rw [domains_card]
  exact Finset.card_image_le

/-- Exact slot dependence for the canonical leaves, with a supplied late-run locality proof. -/
theorem leaf_depends_on (D : S18.LateData hPT) (δ : ℝ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (L : LeafKey D) (x x' : D.encoding.InitInput)
    (hdom : ∀ s ∈ domains D L.1, x.1 s.1 s.2 = x'.1 s.1 s.2)
    (htapes : ∀ C ∈ requirementRegion D L.1, x.2 C = x'.2 C) :
    x ∈ leaf D δ L ↔ x' ∈ leaf D δ L := by
  have hp : ∀ C ∈ requirementRegion D L.1, x.1 C = x'.1 C := by
    intro C hC
    funext s
    exact hdom ⟨C, s⟩ ((mem_domains D L.1 _).2 hC)
  have hrestrict : restrictPools D L.1 x = restrictPools D L.1 x' := by
    funext C
    exact hp C.1 C.2
  rw [mem_leaf, mem_leaf, hrestrict]
  exact and_congr Iff.rfl (terminalFailure_local D δ hlate L.1 x x'
    (fun C hC => ⟨hp C hC, htapes C hC⟩))

private theorem probability_fiber_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : FinLaw Ω) (key : Ω → I) (A : Ω → Prop) (B : I → Prop) :
    (∑ i, if B i then P.pr (fun x => key x = i ∧ A x) else 0) =
      P.pr (fun x => A x ∧ B (key x)) := by
  classical
  have hswap : ∀ i, (if B i then P.pr (fun x => key x = i ∧ A x) else 0) =
      ∑ x, if B i ∧ key x = i ∧ A x then P.w x else 0 := by
    intro i
    by_cases hi : B i
    · simp only [hi, ite_true, FinLaw.pr, true_and]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : key x = i ∧ A x <;> simp [h]
    · simp [hi, FinLaw.pr]
  simp_rw [hswap]
  rw [Finset.sum_comm]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_eq_single (key x)]
  · by_cases ha : A x <;> by_cases hb : B (key x) <;> simp [ha, hb]
  · intro i hi hne
    have hne' : key x ≠ i := Ne.symm hne
    simp [hne']
  · simp

/-- Summing the pool-image slices recovers the actual bad requirement,
also after intersection with any one-slot pin or another event. -/
theorem leaf_probability_partition (D : S18.LateData hPT) (δ : ℝ)
    (f : S18.TerminalIndex D) (A : D.encoding.InitInput → Prop) :
    (∑ p : PoolSlice D f, D.encoding.permLaw.pr (fun x => A x ∧ x ∈ leaf D δ ⟨f, p⟩)) =
      D.encoding.permLaw.pr (fun x => A x ∧ S18.terminalFailure D δ f x) := by
  have h := probability_fiber_sum D.encoding.permLaw (restrictPools D f)
    (fun x => A x ∧ S18.terminalFailure D δ f x) (fun _ => True)
  have heq : ∀ p : PoolSlice D f,
      D.encoding.permLaw.pr (fun x => A x ∧ x ∈ leaf D δ ⟨f, p⟩) =
      D.encoding.permLaw.pr (fun x => restrictPools D f x = p ∧
        (A x ∧ S18.terminalFailure D δ f x)) := by
    intro p
    congr 1
    funext x
    exact propext (by rw [mem_leaf]; tauto)
  simp_rw [heq]
  simpa using h

def imageAt (D : S18.LateData hPT) (x : D.encoding.InitInput)
    (s : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)) :
    Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i :=
  ⟨D.geom.cellPatch s.1, x.1 s.1 s.2⟩

theorem images_restrict (D : S18.LateData hPT) (f : S18.TerminalIndex D)
    (x : D.encoding.InitInput) :
    images D ⟨f, restrictPools D f x⟩ = (domains D f).image (imageAt D x) := by
  rw [domains, Finset.image_image]
  rfl

theorem images_of_mem_leaf (D : S18.LateData hPT) (δ : ℝ) (L : LeafKey D)
    (x : D.encoding.InitInput) (hx : x ∈ leaf D δ L) :
    images D L = (domains D L.1).image (imageAt D x) := by
  cases L with
  | mk f p =>
    have hp := ((mem_leaf D δ ⟨f, p⟩ x).1 hx).1
    change restrictPools D f x = p at hp
    change images D ⟨f, p⟩ = (domains D f).image (imageAt D x)
    rw [← hp]
    exact images_restrict D f x

theorem image_leaf_probability_partition (D : S18.LateData hPT) (δ : ℝ)
    (f : S18.TerminalIndex D)
    (b : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :
    (∑ p : PoolSlice D f,
      if b ∈ images D ⟨f, p⟩ then D.encoding.permLaw.pr (fun x => x ∈ leaf D δ ⟨f, p⟩) else 0) =
      D.encoding.permLaw.pr (fun x => S18.terminalFailure D δ f x ∧
        b ∈ (domains D f).image (imageAt D x)) := by
  have h := probability_fiber_sum D.encoding.permLaw (restrictPools D f)
    (S18.terminalFailure D δ f) (fun p => b ∈ images D ⟨f, p⟩)
  have heq : ∀ p : PoolSlice D f,
      D.encoding.permLaw.pr (fun x => x ∈ leaf D δ ⟨f, p⟩) =
      D.encoding.permLaw.pr (fun x => restrictPools D f x = p ∧ S18.terminalFailure D δ f x) := by
    intro p
    congr 1
    funext x
    exact propext (mem_leaf D δ ⟨f, p⟩ x)
  simp_rw [heq]
  simp_rw [images_restrict] at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hb : b ∈ images D ⟨f, p⟩ <;> simp [hb]

private theorem probability_image_union_le {Ω A B : Type*}
    [Fintype Ω] [DecidableEq A] [DecidableEq B]
    (P : FinLaw Ω) (S : Finset A) (g : Ω → A → B) (bad : Ω → Prop) (b : B) :
    P.pr (fun x => bad x ∧ b ∈ S.image (g x)) ≤
      ∑ a ∈ S, P.pr (fun x => g x a = b ∧ bad x) := by
  classical
  unfold FinLaw.pr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  by_cases h : bad x ∧ b ∈ S.image (g x)
  · obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp h.2
    rw [if_pos h]
    have hl := Finset.single_le_sum
      (f := fun a => if g x a = b ∧ bad x then P.w x else 0)
      (fun a _ => by split_ifs <;> simp [P.nonneg]) ha
    simpa only [hab, h.1, and_self, ite_true] using hl
  · rw [if_neg h]
    exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [P.nonneg]

private theorem pr_nonneg {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    0 ≤ P.pr A := by
  unfold FinLaw.pr
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [P.nonneg]

private theorem pr_inter_le {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A B : Ω → Prop) : P.pr (fun x => A x ∧ B x) ≤ P.pr A := by
  unfold FinLaw.pr
  apply Finset.sum_le_sum
  intro x hx
  by_cases ha : A x <;> by_cases hb : B x <;> simp [ha, hb, P.nonneg]

private theorem joint_bound_of_conditional {Ω : Type*} [Fintype Ω]
    (P : FinLaw Ω) (A B : Ω → Prop) (q : ℝ)
    (h : P.pr (fun x => A x ∧ B x) / P.pr A ≤ q) :
    P.pr (fun x => A x ∧ B x) ≤ P.pr A * q := by
  by_cases hpos : 0 < P.pr A
  · have hh := (div_le_iff₀ hpos).1 h
    simpa only [mul_comm] using hh
  · have hz : P.pr A = 0 := le_antisymm (le_of_not_gt hpos) (pr_nonneg P A)
    have hjoint : P.pr (fun x => A x ∧ B x) = 0 := by
      exact le_antisymm (hz ▸ pr_inter_le P A B) (pr_nonneg P _)
    rw [hz, hjoint, zero_mul]

theorem terminal_pin_joint_bound (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (f : S18.TerminalIndex D) (p : S18.SlotPin D) :
    D.encoding.permLaw.pr (fun x => S18.pinEvent D p x ∧ S18.terminalFailure D δ f x) ≤
      D.encoding.permLaw.pr (S18.pinEvent D p) *
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  exact joint_bound_of_conditional _ _ _ _ (hRisk (some p) f)

/-- Charging a fixed image uses the one-slot bound even when the slot's cell
is far from that image's other users. Null pins also satisfy this estimate. -/
theorem image_slot_joint_bound (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (f : S18.TerminalIndex D)
    (s : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C))
    (b : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :
    D.encoding.permLaw.pr (fun x => imageAt D x s = b ∧ S18.terminalFailure D δ f x) ≤
      D.encoding.permLaw.pr (fun x => imageAt D x s = b) *
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  cases b with
  | mk i b =>
    by_cases hi : D.geom.cellPatch s.1 = i
    · subst i
      have heq : ∀ x, imageAt D x s = ⟨D.geom.cellPatch s.1, b⟩ ↔
          S18.pinEvent D ⟨s.1, s.2, b⟩ x := by
        intro x
        simp [imageAt, S18.pinEvent]
      simpa only [heq] using terminal_pin_joint_bound D δ hRisk f ⟨s.1, s.2, b⟩
    · have hne : ∀ x, imageAt D x s ≠ ⟨i, b⟩ := by
        intro x heq
        exact hi (congrArg Sigma.fst heq)
      simp [hne, FinLaw.pr]

theorem image_leaf_probability_bound (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (f : S18.TerminalIndex D)
    (b : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :
    (∑ p : PoolSlice D f,
      if b ∈ images D ⟨f, p⟩ then D.encoding.permLaw.pr (fun x => x ∈ leaf D δ ⟨f, p⟩) else 0) ≤
      (∑ s ∈ domains D f, D.encoding.permLaw.pr (fun x => imageAt D x s = b)) *
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  rw [image_leaf_probability_partition]
  calc
    _ ≤ ∑ s ∈ domains D f,
        D.encoding.permLaw.pr (fun x => imageAt D x s = b ∧ S18.terminalFailure D δ f x) :=
      probability_image_union_le _ _ _ _ _
    _ ≤ ∑ s ∈ domains D f,
        D.encoding.permLaw.pr (fun x => imageAt D x s = b) *
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) :=
      Finset.sum_le_sum fun s _ => image_slot_joint_bound D δ hRisk f s b
    _ = _ := (Finset.sum_mul _ _ _).symm

def HistoryAgrees (D : S18.LateData hPT) (cells : Finset D.geom.Cell)
    (rows : Finset (Pos T k)) {j : Fin (D.geom.r + 1)}
    (h h' : D.encoding.base.History j) : Prop :=
  (∀ C ∈ cells, h.1 C = h'.1 C) ∧
    ∀ b : D.encoding.base.ProcessedRole j, b.1 ∈ rows → h.2 b = h'.2 b

private theorem law_nonempty {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : Nonempty Ω := by
  have hsum : (∑ x, P.w x) ≠ 0 := by rw [P.sum_one]; exact one_ne_zero
  obtain ⟨x, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  exact ⟨x⟩

private theorem map_expectation {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun x => g (f x)) := by
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

private theorem bind_expectation {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (g : α × β → ℝ) :
    (FinLaw.bind P K).E g = P.E (fun x => (K x).E (fun y => g (x, y))) := by
  simp only [FinLaw.E, FinLaw.bind, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem dirac_expectation {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (x : Ω) (g : Ω → ℝ) :
    (FinLaw.dirac x).E g = g x := by
  unfold FinLaw.E FinLaw.dirac
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hne
    simp [hne]
  · simp

theorem extend_agrees (D : S18.LateData hPT) (cells : Finset D.geom.Cell)
    (rows : Finset (Pos T k)) (j : Fin D.geom.r)
    (h h' : D.encoding.base.History j.castSucc)
    (hh : HistoryAgrees D cells rows h h')
    (out out' : D.encoding.base.ClassRows j)
    (ho : ∀ b, b.1 ∈ rows → out b = out' b) :
    HistoryAgrees D cells rows (D.encoding.base.extend j h out)
      (D.encoding.base.extend j h' out') := by
  refine ⟨hh.1, ?_⟩
  intro b hb
  dsimp [LateProcessBase.extend]
  split_ifs with hp
  · exact hh.2 ⟨b.1, hp⟩ hb
  · exact ho _ hb

/-- A reference-class expectation depends only on the kernels of the rows
consulted by its test. The entering histories may differ everywhere else. -/
theorem reference_step_local (D : S18.LateData hPT)
    (cells : Finset D.geom.Cell) (past next : Finset (Pos T k))
    (hsub : next ⊆ past) (j : Fin D.geom.r)
    (h h' : D.encoding.base.History j.castSucc)
    (hh : HistoryAgrees D cells past h h')
    (hK : ∀ b, b.1 ∈ next → D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h')
    (g : D.encoding.base.History j.succ → ℝ)
    (hg : ∀ z z', HistoryAgrees D cells next z z' → g z = g z') :
    (D.encoding.kernels.referenceTransition j h).E
      (fun out => g (D.encoding.base.extend j h out)) =
    (D.encoding.kernels.referenceTransition j h').E
      (fun out => g (D.encoding.base.extend j h' out)) := by
  let scope := Finset.univ.filter fun b : {b : Pos T k // b ∈ D.encoding.base.classes j} => b.1 ∈ next
  letI : ∀ b : {b : Pos T k // b ∈ D.encoding.base.classes j}, Nonempty (D.encoding.base.RowOut b.1) :=
    fun b => law_nonempty (D.encoding.kernels.refK j b h)
  have hhnext : HistoryAgrees D cells next h h' :=
    ⟨hh.1, fun b hb => hh.2 b (hsub hb)⟩
  have hf : ∀ out out', (∀ b ∈ scope, out b = out' b) →
      g (D.encoding.base.extend j h out) = g (D.encoding.base.extend j h out') := by
    intro out out' ho
    exact hg _ _ (extend_agrees D cells next j h h ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      out out' (fun b hb => ho b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)))
  have hchange := S18.Lane_sol_s18_n5.pi_E_local
    (fun b => D.encoding.kernels.refK j b h) (fun b => D.encoding.kernels.refK j b h')
    scope (fun out => g (D.encoding.base.extend j h out)) hf
    (fun b hb => hK b (Finset.mem_filter.mp hb).2)
  change (FinLaw.pi _).E _ = (FinLaw.pi _).E _
  rw [hchange]
  congr 1
  funext out
  exact hg _ _ (extend_agrees D cells next j h h' hhnext out out (fun _ _ => rfl))

/-- Backward integration through the actual product reference run. A nested
row-scope family and local row kernels suffice; no global kernel equality is needed. -/
theorem reference_run_local (D : S18.LateData hPT) (cells : Finset D.geom.Cell)
    (rows : Fin (D.geom.r + 1) → Finset (Pos T k))
    (hsub : ∀ j : Fin D.geom.r, rows j.succ ⊆ rows j.castSucc)
    (hK : ∀ (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
      (h h' : D.encoding.base.History j.castSucc),
      HistoryAgrees D cells (rows j.castSucc) h h' → b.1 ∈ rows j.succ →
      D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h')
    (s s' : Config D.fresh) (hs : ∀ C ∈ cells, s C = s' C) :
    ∀ m (hm : m ≤ D.geom.r) (g : D.encoding.base.History ⟨m, Nat.lt_succ_of_le hm⟩ → ℝ),
      (∀ h h', HistoryAgrees D cells (rows ⟨m, Nat.lt_succ_of_le hm⟩) h h' → g h = g h') →
      (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s m hm).E g =
        (D.encoding.base.runFrom D.encoding.kernels.referenceTransition s' m hm).E g := by
  intro m
  induction m with
  | zero =>
    intro hm g hg
    change (FinLaw.dirac (D.encoding.base.initialHistory s)).E
      (show D.encoding.base.History 0 → ℝ from g) =
        (FinLaw.dirac (D.encoding.base.initialHistory s')).E
          (show D.encoding.base.History 0 → ℝ from g)
    rw [dirac_expectation, dirac_expectation]
    apply hg
    refine ⟨hs, ?_⟩
    intro b hb
    have hnone : False := by simpa [D.encoding.base.processed_zero] using b.2
    exact hnone.elim
  | succ m ih =>
    intro hm g hg
    rw [LateProcessBase.runFrom, LateProcessBase.runFrom, map_expectation, map_expectation,
      bind_expectation, bind_expectation]
    apply ih (Nat.le_of_succ_le hm)
    intro h h' hh
    exact reference_step_local D cells (rows (⟨m, hm⟩ : Fin D.geom.r).castSucc)
      (rows (⟨m, hm⟩ : Fin D.geom.r).succ) (hsub ⟨m, hm⟩) ⟨m, hm⟩ h h' hh
      (fun b hb => hK ⟨m, hm⟩ b h h' hh hb) g hg

theorem reference_kernel_agrees (D : S18.LateData hPT) (hD : D.Spec)
    (H : S18.TransitionData D) (cells : Finset D.geom.Cell) (rows : Finset (Pos T k))
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h h' : D.encoding.base.History j.castSucc) (hh : HistoryAgrees D cells rows h h')
    (hcells : ∀ a, D.directCells (flipPos b.1 a) ⊆ cells)
    (hrows : ∀ a (p : D.encoding.base.ProcessedRole j.castSucc),
      (OAI.HypercubeRamsey.cube (T.S.n k)).Adj (flipPos b.1 a) p.1 → p.1 ∈ rows) :
    D.encoding.kernels.refK j b h = D.encoding.kernels.refK j b h' := by
  apply Lane_sol_s18_n4.referenceRow_local D H j b h h'
  intro a
  apply Lane_sol_s18_n4.priorAt_local D hD j.castSucc (flipPos b.1 a) h h'
  · intro C hC
    exact hh.1 C (hcells a hC)
  · intro p hp
    rw [hh.2 p (hrows a p hp)]

noncomputable def incidentRequirements (D : S18.LateData hPT) (C : D.geom.Cell) :
    Finset (S18.TerminalIndex D) :=
  Finset.univ.filter fun f => C ∈ requirementRegion D f

theorem imageAt_injective (D : S18.LateData hPT) (x : D.encoding.InitInput)
    (hx : x.1 ∈ permPools D.geom) : Function.Injective (imageAt D x) := by
  intro s t heq
  have hp : D.geom.cellPatch s.1 = D.geom.cellPatch t.1 := congrArg Sigma.fst heq
  have hb : (x.1 s.1 s.2).1 = (x.1 t.1 t.2).1 :=
    congrArg (fun b : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i => b.2.1) heq
  have h := (Finset.mem_filter.mp hx).2 s.1 t.1 s.2 t.2 hp hb
  cases s with
  | mk C s =>
    cases t with
    | mk C' t =>
      dsimp at h
      rcases h with ⟨rfl, hs⟩
      have hst : s = t := Fin.ext hs
      cases hst
      rfl

theorem pool_support_of_positive (D : S18.LateData hPT) (x : D.encoding.InitInput)
    (hx : 0 < D.encoding.permLaw.w x) : x.1 ∈ permPools D.geom := by
  by_contra hn
  have hz : D.encoding.permLaw.w x = 0 := by
    simp [LateEncoding.permLaw, LateEncoding.initialLaw, LateEncoding.poolLaw,
      permPoolLaw, FinLaw.bind, FinLaw.uniform, hn]
  rw [hz] at hx
  exact (lt_irrefl 0) hx

/-- A used image has only one domain slot on permutation support. Thus the
sum of expected image incidences is bounded by the deterministic requirement
incidence at that slot's cell, without any independence assumption. -/
theorem image_incidence_mass_bound (D : S18.LateData hPT) (M : ℕ)
    (hinc : ∀ C, (incidentRequirements D C).card ≤ M)
    (b : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :
    (∑ f : S18.TerminalIndex D, ∑ s ∈ domains D f,
      D.encoding.permLaw.pr (fun x => imageAt D x s = b)) ≤ (M : ℝ) := by
  let P := D.encoding.permLaw
  have hrewrite : (∑ f : S18.TerminalIndex D, ∑ s ∈ domains D f,
      P.pr (fun x => imageAt D x s = b)) =
      ∑ x, ∑ f : S18.TerminalIndex D, ∑ s ∈ domains D f,
        if imageAt D x s = b then P.w x else 0 := by
    unfold FinLaw.pr
    calc
      _ = ∑ f : S18.TerminalIndex D, ∑ s ∈ domains D f, ∑ x,
          if imageAt D x s = b then P.w x else 0 := by
        apply Finset.sum_congr rfl
        intro f hf
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hb : imageAt D x s = b <;> simp [hb]
      _ = ∑ f : S18.TerminalIndex D, ∑ x, ∑ s ∈ domains D f,
          if imageAt D x s = b then P.w x else 0 :=
        Finset.sum_congr rfl (fun f _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hrewrite]
  calc
    _ ≤ ∑ x, P.w x * (M : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      by_cases hw : P.w x = 0
      · simp [hw]
      have hwpos : 0 < P.w x := lt_of_le_of_ne (P.nonneg x) (Ne.symm hw)
      have hinj := imageAt_injective D x (pool_support_of_positive D x hwpos)
      by_cases hex : ∃ s, imageAt D x s = b
      · obtain ⟨s₀, hs₀⟩ := hex
        have hkey : ∀ s, imageAt D x s = b ↔ s = s₀ := by
          intro s
          constructor
          · intro hs
            exact hinj (hs.trans hs₀.symm)
          · rintro rfl
            exact hs₀
        have hsum : ∀ f : S18.TerminalIndex D,
            (∑ s ∈ domains D f, if imageAt D x s = b then P.w x else 0) =
              if s₀.1 ∈ requirementRegion D f then P.w x else 0 := by
          intro f
          by_cases hs : s₀ ∈ domains D f
          · simp only [(mem_domains D f s₀).1 hs, ite_true]
            rw [Finset.sum_eq_single s₀]
            · simp [hs₀]
            · intro s hsd hne
              have hne' : imageAt D x s ≠ b := fun h => hne ((hkey s).1 h)
              simp [hne']
            · intro hn
              exact (hn hs).elim
          · have hC : s₀.1 ∉ requirementRegion D f := fun h => hs ((mem_domains D f s₀).2 h)
            simp only [hC, ite_false]
            apply Finset.sum_eq_zero
            intro s hsd
            have hne : imageAt D x s ≠ b := by
              intro h
              exact hs ((hkey s).1 h ▸ hsd)
            simp [hne]
        simp_rw [hsum]
        have hcard : (∑ f : S18.TerminalIndex D,
            if s₀.1 ∈ requirementRegion D f then P.w x else 0) =
              ((incidentRequirements D s₀.1).card : ℝ) * P.w x := by
          rw [← Finset.sum_filter]
          simp [incidentRequirements]
        rw [hcard]
        have hM : ((incidentRequirements D s₀.1).card : ℝ) ≤ M := by exact_mod_cast hinc s₀.1
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hM (P.nonneg x)
      · have hnone : ∀ s, imageAt D x s ≠ b := fun s hs => hex ⟨s, hs⟩
        simp only [hnone, ite_false, Finset.sum_const_zero]
        exact mul_nonneg (P.nonneg x) (Nat.cast_nonneg _)
    _ = (M : ℝ) := by rw [← Finset.sum_mul, P.sum_one, one_mul]

theorem image_leaf_incident_bound (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (M : ℕ)
    (hinc : ∀ C, (incidentRequirements D C).card ≤ M)
    (b : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) :
    (∑ L : LeafKey D, if b ∈ images D L then
      D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) else 0) ≤
      (M : ℝ) * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ f : S18.TerminalIndex D,
      (∑ s ∈ domains D f, D.encoding.permLaw.pr (fun x => imageAt D x s = b)) *
        Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) :=
      Finset.sum_le_sum fun f _ => image_leaf_probability_bound D δ hRisk f b
    _ = (∑ f : S18.TerminalIndex D, ∑ s ∈ domains D f,
        D.encoding.permLaw.pr (fun x => imageAt D x s = b)) *
          Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (image_incidence_mass_bound D M hinc b)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem cell_leaf_incident_bound (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (M : ℕ)
    (hinc : ∀ C, (incidentRequirements D C).card ≤ M) (C : D.geom.Cell) :
    (∑ L : LeafKey D, if C ∈ requirementRegion D L.1 then
      D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) else 0) ≤
      (M : ℝ) * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  let q := Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))
  have hq : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpartition (f : S18.TerminalIndex D) :
      (∑ p : PoolSlice D f, D.encoding.permLaw.pr (fun x => x ∈ leaf D δ ⟨f, p⟩)) =
        D.encoding.permLaw.pr (S18.terminalFailure D δ f) := by
    simpa using leaf_probability_partition D δ f (fun _ => True)
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ f : S18.TerminalIndex D, if C ∈ requirementRegion D f then
      D.encoding.permLaw.pr (S18.terminalFailure D δ f) else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hC : C ∈ requirementRegion D f
      · simp only [hC, ite_true]
        exact hpartition f
      · simp [hC]
    _ ≤ ∑ f : S18.TerminalIndex D, if C ∈ requirementRegion D f then q else 0 := by
      apply Finset.sum_le_sum
      intro f hf
      by_cases hC : C ∈ requirementRegion D f
      · simp only [hC, ite_true]
        exact hRisk none f
      · simp [hC]
    _ = ((incidentRequirements D C).card : ℝ) * q := by
      rw [← Finset.sum_filter]
      simp [incidentRequirements]
    _ ≤ (M : ℝ) * q := mul_le_mul_of_nonneg_right (by exact_mod_cast hinc C) hq

theorem domain_leaf_incident_bound (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (M : ℕ)
    (hinc : ∀ C, (incidentRequirements D C).card ≤ M)
    (s : Sigma fun C : D.geom.Cell => Fin (D.geom.nslot C)) :
    (∑ L : LeafKey D, if s ∈ domains D L.1 then
      D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) else 0) ≤
      (M : ℝ) * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3)) := by
  have heq : (∑ L : LeafKey D, if s ∈ domains D L.1 then
      D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) else 0) =
      ∑ L : LeafKey D, if s.1 ∈ requirementRegion D L.1 then
        D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) else 0 := by
    apply Finset.sum_congr rfl
    intro L hL
    by_cases hs : s ∈ domains D L.1
    · simp [hs, (mem_domains D L.1 s).1 hs]
    · have hC : s.1 ∉ requirementRegion D L.1 := by simpa only [mem_domains] using hs
      simp [hs, hC]
  rw [heq]
  exact cell_leaf_incident_bound D δ hRisk M hinc s.1

noncomputable def adjacent (D : S18.LateData hPT) (L L' : LeafKey D) : Prop :=
  ¬ Disjoint (domains D L.1) (domains D L'.1) ∨
    ¬ Disjoint (images D L) (images D L') ∨
    ¬ Disjoint (requirementRegion D L.1) (requirementRegion D L'.1)

private theorem twice_incident_sum {I : Type*} [Fintype I]
    (B : I → Prop) [DecidablePred B] (p : I → ℝ) :
    (∑ i, if B i then 2 * p i else 0) = 2 * ∑ i, if B i then p i else 0 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : B i <;> simp [h]

/-- All three kinds of token pay the same deterministic incidence bound.
Image tokens use the pinned estimates and injective permutation support. -/
theorem leaf_touching_charge (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (M : ℕ)
    (hinc : ∀ C, (incidentRequirements D C).card ≤ M) (L : LeafKey D) :
    (∑ L' : LeafKey D, if adjacent D L L' then
      2 * D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L') else 0) ≤
      (((domains D L.1).card + (images D L).card +
        (requirementRegion D L.1).card : ℕ) : ℝ) *
        (2 * (M : ℝ) * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))) := by
  let charge := fun i : LeafKey D => 2 * D.encoding.permLaw.pr (fun x => x ∈ leaf D δ i)
  let B := 2 * (M : ℝ) * Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))
  have hcharge : ∀ i, 0 ≤ charge i := fun i => mul_nonneg (by norm_num) (pr_nonneg _ _)
  have hdom : (∑ i : LeafKey D, if ¬ Disjoint (domains D i.1) (domains D L.1)
      then charge i else 0) ≤ ((domains D L.1).card : ℝ) * B := by
    apply Lane_sol_s18_n4.testTouchingCharge _ _ hcharge _ B
    intro s hs
    unfold charge
    rw [twice_incident_sum]
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left
      (domain_leaf_incident_bound D δ hRisk M hinc s) (by norm_num : (0 : ℝ) ≤ 2)
  have himage : (∑ i : LeafKey D, if ¬ Disjoint (images D i) (images D L)
      then charge i else 0) ≤ ((images D L).card : ℝ) * B := by
    apply Lane_sol_s18_n4.testTouchingCharge _ _ hcharge _ B
    intro b hb
    unfold charge
    rw [twice_incident_sum]
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left
      (image_leaf_incident_bound D δ hRisk M hinc b) (by norm_num : (0 : ℝ) ≤ 2)
  have htape : (∑ i : LeafKey D, if ¬ Disjoint (requirementRegion D i.1) (requirementRegion D L.1)
      then charge i else 0) ≤ ((requirementRegion D L.1).card : ℝ) * B := by
    apply Lane_sol_s18_n4.testTouchingCharge _ _ hcharge _ B
    intro C hC
    unfold charge
    rw [twice_incident_sum]
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_left
      (cell_leaf_incident_bound D δ hRisk M hinc C) (by norm_num : (0 : ℝ) ≤ 2)
  change (∑ i, if adjacent D L i then charge i else 0) ≤ _
  calc
    _ ≤ (∑ i : LeafKey D, if ¬ Disjoint (domains D i.1) (domains D L.1) then charge i else 0) +
        (∑ i : LeafKey D, if ¬ Disjoint (images D i) (images D L) then charge i else 0) +
        (∑ i : LeafKey D, if ¬ Disjoint (requirementRegion D i.1) (requirementRegion D L.1)
          then charge i else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro i hi
      have hds : Disjoint (domains D L.1) (domains D i.1) ↔
          Disjoint (domains D i.1) (domains D L.1) := disjoint_comm
      have hbs : Disjoint (images D L) (images D i) ↔ Disjoint (images D i) (images D L) := disjoint_comm
      have hts : Disjoint (requirementRegion D L.1) (requirementRegion D i.1) ↔
          Disjoint (requirementRegion D i.1) (requirementRegion D L.1) := disjoint_comm
      simp only [adjacent, hds, hbs, hts]
      by_cases hd : Disjoint (domains D i.1) (domains D L.1) <;>
        by_cases hb : Disjoint (images D i) (images D L) <;>
        by_cases ht : Disjoint (requirementRegion D i.1) (requirementRegion D L.1) <;>
        simp only [hd, hb, ht, not_true_eq_false, not_false_eq_true, false_or, true_or,
          or_true, or_false, ite_true, ite_false] <;> linarith [hcharge i]
    _ ≤ _ := add_le_add (add_le_add hdom himage) htape
    _ = _ := by
      change _ = (((domains D L.1).card + (images D L).card +
        (requirementRegion D L.1).card : ℕ) : ℝ) * B
      push_cast
      ring

noncomputable def scopeBudget (D : S18.LateData hPT) : ℝ :=
  Real.rpow (T.S.n k : ℝ) (10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ))

/-- The remaining concrete construction inputs. The leaf table, exact
dependency, image charges and lopsided consequence are derived below. -/
structure CanonicalLeafInputs (D : S18.LateData hPT) (δ : ℝ) where
  scope : ∀ L : LeafKey D,
    (((domains D L.1).card + (images D L).card +
      (requirementRegion D L.1).card : ℕ) : ℝ) ≤ scopeBudget D
  incidence : ∀ C, (incidentRequirements D C).card ≤ ⌊scopeBudget D⌋₊
  force : ∀ L : LeafKey D, 0 < ∑ x ∈ leaf D δ L, D.encoding.permLaw.w x →
    D.encoding.InitInput → FinLaw D.encoding.InitInput
  pushforward : ∀ L hL,
    FinLaw.map (FinLaw.bind D.encoding.permLaw (force L hL)) Prod.snd =
      FinLaw.cond D.encoding.permLaw (leaf D δ L) hL
  preserves : ∀ L hL x y, 0 < (force L hL x).w y → ∀ L',
    ¬ adjacent D L L' → x ∈ leaf D δ L' → y ∈ leaf D δ L'

theorem canonical_touching_charge (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (X : CanonicalLeafInputs D δ)
    (hn : 0 < (T.S.n k : ℝ)) (L : LeafKey D) :
    (∑ L' : LeafKey D, if adjacent D L L' then
      2 * D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L') else 0) ≤
      2 * Real.rpow (T.S.n k : ℝ)
        (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
          (κ.P : ℝ) * D.encoding.Ts / 3) := by
  let B := scopeBudget D
  let q := Real.rpow (T.S.n k : ℝ) (-((κ.P : ℝ) * D.encoding.Ts / 3))
  have hB : 0 ≤ B := Real.rpow_nonneg hn.le _
  have hq : 0 ≤ q := Real.rpow_nonneg hn.le _
  have hM : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
  have hpow : B * B * q = Real.rpow (T.S.n k : ℝ)
      (20 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) -
        (κ.P : ℝ) * D.encoding.Ts / 3) := by
    dsimp [B, scopeBudget, q]
    rw [← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ (((domains D L.1).card + (images D L).card +
          (requirementRegion D L.1).card : ℕ) : ℝ) * (2 * (⌊B⌋₊ : ℝ) * q) :=
      leaf_touching_charge D δ hRisk _ X.incidence L
    _ ≤ B * (2 * (⌊B⌋₊ : ℝ) * q) := mul_le_mul_of_nonneg_right (X.scope L) (by positivity)
    _ ≤ B * (2 * B * q) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) hq) hB
    _ = 2 * (B * B * q) := by ring
    _ = _ := by rw [hpow]

noncomputable def leafCouplingOfInputs (D : S18.LateData hPT) (δ : ℝ)
    (hRisk : S18.TerminalRiskBound D δ) (X : CanonicalLeafInputs D δ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (hn : 0 < (T.S.n k : ℝ)) : S18.LeafCoupling D δ where
  Leaf := LeafKey D
  leaf := leaf D δ
  requirement := Sigma.fst
  domains := fun L => domains D L.1
  images := images D
  tapes := fun L => requirementRegion D L.1
  covers := leaf_covers D δ
  adjacent := adjacent D
  adjacent_eq := fun _ _ => Iff.rfl
  depends_on := leaf_depends_on D δ hlate
  scope_bound := by
    intro L
    simpa only [scopeBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using X.scope L
  touching_charge := canonical_touching_charge D δ hRisk X hn
  force := X.force
  conditional_pushforward := X.pushforward
  preserves := X.preserves
  nonneighbor_bound := Lane_sol_s18_n4.leafNonneighborBoundOfForcing D
    (leaf D δ) (adjacent D) X.force X.pushforward X.preserves

noncomputable def poolSliceSet (D : S18.LateData hPT) (L : LeafKey D) :
    Finset (∀ C, D.fresh.Pool C) :=
  Finset.univ.filter fun p => (fun C : {C // C ∈ requirementRegion D L.1} => p C.1) = L.2

noncomputable def tapeSliceSet (D : S18.LateData hPT) (δ : ℝ) (L : LeafKey D)
    (target : D.encoding.InitInput) : Finset (Tapes D.fresh D.encoding.Ts) :=
  Finset.univ.filter fun t => S18.terminalFailure D δ L.1 (target.1, t)

theorem leaf_factorization (D : S18.LateData hPT) (δ : ℝ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (L : LeafKey D) (target : D.encoding.InitInput)
    (htarget : restrictPools D L.1 target = L.2) (x : D.encoding.InitInput) :
    x ∈ leaf D δ L ↔ x.1 ∈ poolSliceSet D L ∧ x.2 ∈ tapeSliceSet D δ L target := by
  have hpin : x.1 ∈ poolSliceSet D L ↔ restrictPools D L.1 x = L.2 := by
    simp only [poolSliceSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have htape : x.2 ∈ tapeSliceSet D δ L target ↔
      S18.terminalFailure D δ L.1 (target.1, x.2) := by
    simp only [tapeSliceSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_leaf, hpin, htape]
  apply and_congr_right
  intro hx
  apply terminalFailure_local D δ hlate L.1 x (target.1, x.2)
  intro C hC
  refine ⟨?_, rfl⟩
  exact (congrFun hx ⟨C, hC⟩).trans (congrFun htarget ⟨C, hC⟩).symm

theorem tape_slice_local (D : S18.LateData hPT) (δ : ℝ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (L : LeafKey D) (target : D.encoding.InitInput)
    (t t' : Tapes D.fresh D.encoding.Ts)
    (ht : ∀ C ∈ requirementRegion D L.1, t C = t' C) :
    t ∈ tapeSliceSet D δ L target ↔ t' ∈ tapeSliceSet D δ L target := by
  simp only [tapeSliceSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact terminalFailure_local D δ hlate L.1 (target.1, t) (target.1, t')
    (fun C hC => ⟨rfl, ht C hC⟩)

/-- Any positive canonical leaf has an actual permutation-support representative,
so its prescribed partial mappings can be completed to valid patch injections. -/
theorem positive_leaf_representative (D : S18.LateData hPT) (δ : ℝ) (L : LeafKey D)
    (hpos : 0 < ∑ x ∈ leaf D δ L, D.encoding.permLaw.w x) :
    ∃ x, x ∈ leaf D δ L ∧ 0 < D.encoding.permLaw.w x ∧ x.1 ∈ permPools D.geom := by
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hpos)
  have hw : 0 < D.encoding.permLaw.w x := lt_of_le_of_ne (D.encoding.permLaw.nonneg x) (Ne.symm hne)
  exact ⟨x, hx, hw, pool_support_of_positive D x hw⟩

/-- Pools and tapes are independent in the actual initial experiment. After
fixing the consulted pool images, the leaf's remaining event is a tape event. -/
theorem leaf_probability_factorization (D : S18.LateData hPT) (δ : ℝ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (L : LeafKey D) (target : D.encoding.InitInput)
    (htarget : restrictPools D L.1 target = L.2) :
    D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) =
      D.encoding.poolLaw.pr (fun p => p ∈ poolSliceSet D L) *
        (tapeLaw D.fresh D.encoding.Ts).pr (fun t => t ∈ tapeSliceSet D δ L target) := by
  let P := D.encoding.poolLaw
  let Q := tapeLaw D.fresh D.encoding.Ts
  have hleft : D.encoding.permLaw.pr (fun x => x ∈ leaf D δ L) =
      ∑ p, ∑ t, if (p, t) ∈ leaf D δ L then P.w p * Q.w t else 0 := by
    unfold LateEncoding.permLaw LateEncoding.initialLaw FinLaw.pr FinLaw.bind
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : (p, t) ∈ leaf D δ L <;> simp only [h, ite_true, ite_false] <;> rfl
  rw [hleft]
  have hterm : ∀ p t, (if (p, t) ∈ leaf D δ L then P.w p * Q.w t else 0) =
      (if p ∈ poolSliceSet D L then P.w p else 0) *
        (if t ∈ tapeSliceSet D δ L target then Q.w t else 0) := by
    intro p t
    have h := leaf_factorization D δ hlate L target htarget (p, t)
    by_cases hp : p ∈ poolSliceSet D L <;>
      by_cases ht : t ∈ tapeSliceSet D δ L target <;> simp [h, hp, ht]
  simp_rw [hterm]
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  congr 1
  · unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p ∈ poolSliceSet D L <;> simp only [h, ite_true, ite_false] <;> rfl
  · unfold FinLaw.pr
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : t ∈ tapeSliceSet D δ L target <;> simp only [h, ite_true, ite_false] <;> rfl

private theorem cube_flip_distance {n : ℕ} (v : CubePos n) (a : Fin n) :
    hammingDist v (flipPos v a) = 1 := by
  have heq : (Finset.univ.filter fun j : Fin n => v j ≠ flipPos v a j) = {a} := by
    ext j
    by_cases hj : j = a
    · subst j
      cases hv : v a <;> simp [flipPos, hv]
    · have hu : flipPos v a j = v j := Function.update_of_ne hj _ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hu]
      simp [hj]
  change (Finset.univ.filter fun j : Fin n => v j ≠ flipPos v a j).card = 1
  rw [heq, Finset.card_singleton]

private theorem cubeBall_mono {n : ℕ} (b : CubePos n) {R S : ℕ} (hRS : R ≤ S) :
    cubeBall b R ⊆ cubeBall b S := by
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2.trans hRS⟩

private theorem flip_mem_cubeBall {n : ℕ} (b v : CubePos n) (R : ℕ)
    (hv : v ∈ cubeBall b R) (a : Fin n) : flipPos v a ∈ cubeBall b (R + 1) := by
  have hd := hammingDist_triangle b v (flipPos v a)
  rw [cube_flip_distance] at hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.trans (Nat.add_le_add_right (Finset.mem_filter.mp hv).2 1)⟩

private theorem neighbor_mem_cubeBall {n : ℕ} (b v w : CubePos n) (R : ℕ)
    (hv : v ∈ cubeBall b R) (hw : (OAI.HypercubeRamsey.cube n).Adj v w) :
    w ∈ cubeBall b (R + 1) := by
  have hd : hammingDist v w = 1 := hw
  have ht := hammingDist_triangle b v w
  rw [hd] at ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.trans (Nat.add_le_add_right (Finset.mem_filter.mp hv).2 1)⟩

noncomputable def causalCells (D : S18.LateData hPT) (b : Pos T k) : Finset D.geom.Cell :=
  (cubeBall b (10 * D.geom.r)).biUnion D.directCells

noncomputable def causalRows (D : S18.LateData hPT) (b : Pos T k)
    (j : Fin (D.geom.r + 1)) : Finset (Pos T k) :=
  cubeBall b (6 * D.geom.r + 2 + 2 * (D.geom.r - j.val))

/-- The actual reference kernels propagate information at distance at most
two per late class. This is the deterministic horizon for terminal late tests. -/
theorem reference_ball_expectation_local (D : S18.LateData hPT) (hD : D.Spec)
    (H : S18.TransitionData D) (b : Pos T k) (s s' : Config D.fresh)
    (hs : ∀ C ∈ causalCells D b, s C = s' C)
    (g : D.encoding.base.History (Fin.last D.geom.r) → ℝ)
    (hg : ∀ h h', HistoryAgrees D (causalCells D b) (cubeBall b (6 * D.geom.r + 2)) h h' →
      g h = g h') :
    (D.encoding.kernels.refRun s).E g = (D.encoding.kernels.refRun s').E g := by
  have hsub : ∀ j : Fin D.geom.r, causalRows D b j.succ ⊆ causalRows D b j.castSucc := by
    intro j
    apply cubeBall_mono
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hK : ∀ (j : Fin D.geom.r) (v : {v : Pos T k // v ∈ D.encoding.base.classes j})
      (h h' : D.encoding.base.History j.castSucc),
      HistoryAgrees D (causalCells D b) (causalRows D b j.castSucc) h h' →
      v.1 ∈ causalRows D b j.succ →
      D.encoding.kernels.refK j v h = D.encoding.kernels.refK j v h' := by
    intro j v h h' hh hv
    apply reference_kernel_agrees D hD H _ _ j v h h' hh
    · intro a C hC
      refine Finset.mem_biUnion.mpr ⟨flipPos v.1 a, ?_, hC⟩
      have hflip := flip_mem_cubeBall b v.1 _ hv a
      apply cubeBall_mono b (show 6 * D.geom.r + 2 + 2 * (D.geom.r - j.succ.val) + 1 ≤
        10 * D.geom.r by
          have hr := D.l16_valid.r_pos
          simp only [Fin.val_succ]
          omega) hflip
    · intro a p hp
      have hflip := flip_mem_cubeBall b v.1 _ hv a
      have hnear := neighbor_mem_cubeBall b (flipPos v.1 a) p.1 _ hflip hp
      apply cubeBall_mono b (show (6 * D.geom.r + 2 + 2 * (D.geom.r - j.succ.val) + 1) + 1 ≤
        6 * D.geom.r + 2 + 2 * (D.geom.r - j.castSucc.val) by
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega) hnear
  apply reference_run_local D (causalCells D b) (causalRows D b) hsub hK s s' hs D.geom.r le_rfl g
  intro h h' hh
  apply hg h h'
  simpa only [causalRows, Fin.val_last, Nat.sub_self, Nat.mul_zero, Nat.add_zero] using hh

private theorem probability_indicator {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) (A : Ω → Prop) :
    P.pr A = P.E (fun x => if A x then 1 else 0) := by
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro x hx
  by_cases ha : A x <;> simp [ha]

theorem late_probability_local_of_failure_scope (D : S18.LateData hPT) (hD : D.Spec)
    (H : S18.TransitionData D) (F : S18.LateEvent D)
    (hf : ∀ h h', HistoryAgrees D (causalCells D F.2.2.1.1)
      (cubeBall F.2.2.1.1 (6 * D.geom.r + 2)) h h' →
      (S18.lateFailure D F h ↔ S18.lateFailure D F h'))
    (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    D.pLate F x = D.pLate F x' := by
  have hs := S18.Lane_sol_s18_n5.initialState_local D (causalCells D F.2.2.1.1) x x' hx
  unfold S18.LateData.pLate
  rw [probability_indicator, probability_indicator]
  apply reference_ball_expectation_local D hD H F.2.2.1.1 _ _ hs
  intro h h' hh
  exact if_congr (hf h h' hh) rfl rfl

theorem beforeHistory_agrees (D : S18.LateData hPT) (cells : Finset D.geom.Cell)
    (rows : Finset (Pos T k)) {t : Fin (D.geom.r + 1)}
    (h h' : D.encoding.base.History t) (hh : HistoryAgrees D cells rows h h')
    (j : Fin (D.geom.r + 1)) (hj : j.val ≤ t.val) :
    HistoryAgrees D cells rows (D.beforeHistory h j hj) (D.beforeHistory h' j hj) := by
  refine ⟨hh.1, ?_⟩
  intro p hp
  exact hh.2 ⟨p.1, D.processed_mono j t hj p.2⟩ hp

theorem priorAt_agrees_near (D : S18.LateData hPT) (hD : D.Spec) (b : Pos T k)
    {j : Fin (D.geom.r + 1)} (h h' : D.encoding.base.History j)
    (hh : HistoryAgrees D (causalCells D b) (cubeBall b (6 * D.geom.r + 2)) h h')
    (v : Pos T k) (hv : v ∈ cubeBall b (6 * D.geom.r + 1)) :
    D.priorAt j v h = D.priorAt j v h' := by
  apply Lane_sol_s18_n4.priorAt_local D hD j v h h'
  · intro C hC
    apply hh.1 C
    refine Finset.mem_biUnion.mpr ⟨v, ?_, hC⟩
    exact cubeBall_mono b (by have hr := D.l16_valid.r_pos; omega) hv
  · intro p hp
    have hnear := neighbor_mem_cubeBall b v p.1 _ hv hp
    rw [hh.2 p hnear]

theorem gate_agrees (D : S18.LateData hPT) (hD : D.Spec) (b : Pos T k)
    (j : Fin D.geom.r) (h h' : D.encoding.base.History j.castSucc)
    (hh : HistoryAgrees D (causalCells D b) (cubeBall b (6 * D.geom.r + 2)) h h') :
    D.gate j b h ↔ D.gate j b h' := by
  unfold S18.LateData.gate
  apply and_congr
  · apply forall_congr'
    intro w
    apply imp_congr_right
    intro hw
    apply imp_congr_right
    intro hEven
    apply S18.Lane_sol_s18_n5.initialValid_local D hD w h.1 h'.1
    intro C hC
    apply hh.1 C
    exact Finset.mem_biUnion.mpr ⟨w, cubeBall_mono b (by omega) hw, hC⟩
  · apply forall_congr'
    intro s
    apply forall_congr'
    intro hs
    apply forall_congr'
    intro v
    apply imp_congr_right
    intro hv
    have hv' : v.1 ∈ cubeBall b (6 * D.geom.r + 2) := cubeBall_mono b (by omega) hv
    have hout : D.pastRows h s hs v = D.pastRows h' s hs v :=
      hh.2 ⟨v.1, D.class_before s j.castSucc hs v.2⟩ hv'
    have hb := beforeHistory_agrees D _ _ h h' hh s.castSucc (Nat.le_of_lt hs)
    have hcur : ∀ a,
        D.currentPrior s (flipPos v.1 a) (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)) =
          D.currentPrior s (flipPos v.1 a) (D.beforeHistory h' s.castSucc (Nat.le_of_lt hs)) := by
      intro a
      exact priorAt_agrees_near D hD b _ _ hb (flipPos v.1 a) (flip_mem_cubeBall b v.1 _ hv a)
    have hR3 : D.R3 s (D.beforeHistory h s.castSucc (Nat.le_of_lt hs)) (D.pastRows h s hs v) ↔
        D.R3 s (D.beforeHistory h' s.castSucc (Nat.le_of_lt hs)) (D.pastRows h' s hs v) := by
      simp only [S18.LateData.R3, hout]
      simp_rw [hcur]
    exact and_congr hR3 (by rw [hout])

/-- Every component of the actual terminal late failure consults the
prescribed final-history ball: gate, side data, prefix moments and true hits. -/
theorem lateFailure_history_local (D : S18.LateData hPT) (hD : D.Spec)
    (F : S18.LateEvent D) (h h' : D.encoding.base.History (Fin.last D.geom.r))
    (hh : HistoryAgrees D (causalCells D F.2.2.1.1)
      (cubeBall F.2.2.1.1 (6 * D.geom.r + 2)) h h') :
    S18.lateFailure D F h ↔ S18.lateFailure D F h' := by
  let j := F.2.1
  let b := F.2.2.1.1
  have hbefore := beforeHistory_agrees D _ _ h h' hh j.castSucc (Nat.le_of_lt j.isLt)
  have hgate := gate_agrees D hD b j _ _ hbefore
  have hb0 : b ∈ cubeBall b 0 := by simp [cubeBall, hammingDist]
  have hb : b ∈ cubeBall b (6 * D.geom.r + 2) := cubeBall_mono b (by omega) hb0
  have hout : D.pastRows h j j.isLt F.2.2.1 = D.pastRows h' j j.isLt F.2.2.1 :=
    hh.2 ⟨b, D.class_before j (Fin.last D.geom.r) j.isLt F.2.2.1.2⟩ hb
  have hinit : ∀ a, D.initialPrior (flipPos b a) h.1 = D.initialPrior (flipPos b a) h'.1 := by
    intro a
    apply Lane_sol_s18_n4.initialPrior_local D hD
    intro C hC
    apply hh.1 C
    have hnear := flip_mem_cubeBall b b 0 hb0 a
    exact Finset.mem_biUnion.mpr ⟨flipPos b a, cubeBall_mono b
      (by have hr := D.l16_valid.r_pos; omega) hnear, hC⟩
  have hcur : ∀ a,
      D.currentPrior j (flipPos b a) (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) =
        D.currentPrior j (flipPos b a) (D.beforeHistory h' j.castSucc (Nat.le_of_lt j.isLt)) := by
    intro a
    apply priorAt_agrees_near D hD b _ _ hbefore
    exact cubeBall_mono b (by omega) (flip_mem_cubeBall b b 0 hb0 a)
  have hMom : ∀ (side : D.encoding.base.RowOut b) order q a,
      D.prefixMoments j (D.beforeHistory h j.castSucc (Nat.le_of_lt j.isLt)) side order q a ↔
        D.prefixMoments j (D.beforeHistory h' j.castSucc (Nat.le_of_lt j.isLt)) side order q a := by
    intro side order q a
    simp only [S18.LateData.prefixMoments, S18.LateData.beforeHistory]
    rw [hinit a]
  dsimp only [S18.lateFailure, S18.LateData.prefixFailure]
  simp only [S18.LateData.R2, S18.LateData.R3]
  dsimp [j, b] at hgate hout hMom hcur
  simp only [hgate, hout, hMom, hcur]

theorem late_probability_local (D : S18.LateData hPT) (hD : D.Spec)
    (H : S18.TransitionData D) (F : S18.LateEvent D) (x x' : D.encoding.InitInput)
    (hx : ∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) :
    D.pLate F x = D.pLate F x' :=
  late_probability_local_of_failure_scope D hD H F (lateFailure_history_local D hD F) x x' hx

end HypercubeRamsey.Lane_sol_s18_3e
