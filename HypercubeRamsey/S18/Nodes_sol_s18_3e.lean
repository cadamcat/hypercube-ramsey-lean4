import HypercubeRamsey.S18.Nodes_sol_s18_n5
import HypercubeRamsey.S18.Leaf_sol_s18_n4
import HypercubeRamsey.S18.Locality_sol_s18_n4
import HypercubeRamsey.S18.Nodes_sol_s18_3f
import HypercubeRamsey.S18.Nodes_sol_s18_4b

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
  images_cover := by
    intro L x hx s hs
    rw [images_of_mem_leaf D δ L x hx]
    exact Finset.mem_image_of_mem (imageAt D x) hs

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

private theorem graphBall_seed_mono (D : S18.LateData hPT)
    {s t : Finset (Pos T k)} (hst : s ⊆ t) (R : ℕ) :
    D.encoding.events.graphBall s R ⊆ D.encoding.events.graphBall t R := by
  induction R with
  | zero => exact hst
  | succ R ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ih hv)
    · obtain ⟨_, w, hw, hvw⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, w, ih hw, hvw⟩)

private theorem graphBall_step (D : S18.LateData hPT) (s : Finset (Pos T k))
    {v w : Pos T k} {R : ℕ} (hv : v ∈ D.encoding.events.graphBall s R)
    (hw : D.encoding.events.Adjacent w v) :
    w ∈ D.encoding.events.graphBall s (R + 1) :=
  Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, hw⟩)

private theorem graphBall_radius_mono (D : S18.LateData hPT) (s : Finset (Pos T k))
    {R Q : ℕ} (h : R ≤ Q) :
    D.encoding.events.graphBall s R ⊆ D.encoding.events.graphBall s Q := by
  induction h with
  | refl => exact fun _ h => h
  | step h ih => exact fun _ hv => Finset.mem_union_left _ (ih hv)

private theorem graphBall_add (D : S18.LateData hPT)
    (s t : Finset (Pos T k)) (R : ℕ)
    (h : t ⊆ D.encoding.events.graphBall s R) (Q : ℕ) :
    D.encoding.events.graphBall t Q ⊆ D.encoding.events.graphBall s (R + Q) := by
  induction Q with
  | zero => simpa [ListEvent.graphBall] using h
  | succ Q ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact graphBall_radius_mono D s (by omega) (ih hv)
    · obtain ⟨_, w, hw, hvw⟩ := Finset.mem_filter.mp hv
      exact graphBall_step D s (ih hw) hvw

private theorem graphBall_singleton_symm (D : S18.LateData hPT)
    (R : ℕ) (v w : Pos T k) :
    w ∈ D.encoding.events.graphBall {v} R → v ∈ D.encoding.events.graphBall {w} R := by
  induction R generalizing v w with
  | zero => simp only [ListEvent.graphBall, Finset.mem_singleton]; exact Eq.symm
  | succ R ih =>
    intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_union_left _ (ih v w hw)
    · obtain ⟨_, u, hu, hwu⟩ := Finset.mem_filter.mp hw
      have hadj : D.encoding.events.Adjacent u w := ⟨hwu.1.symm, fun h => hwu.2 h.symm⟩
      have hseed : ({u} : Finset (Pos T k)) ⊆ D.encoding.events.graphBall {w} 1 := by
        intro z hz
        have hz' := Finset.mem_singleton.mp hz
        subst z
        exact graphBall_step D {w} (by simp [ListEvent.graphBall]) hadj
      simpa only [Nat.add_comm] using graphBall_add D {w} {u} 1 hseed R (ih v u hu)

private theorem graphBall_mem_seed (D : S18.LateData hPT)
    (s : Finset (Pos T k)) (R : ℕ) (v : Pos T k) :
    v ∈ D.encoding.events.graphBall s R ↔
      ∃ w ∈ s, v ∈ D.encoding.events.graphBall {w} R := by
  induction R generalizing v with
  | zero => simp only [ListEvent.graphBall, Finset.mem_singleton]; aesop
  | succ R ih =>
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨w, hw, hvw⟩ := (ih v).1 hv
        exact ⟨w, hw, Finset.mem_union_left _ hvw⟩
      · obtain ⟨_, u, hu, hvu⟩ := Finset.mem_filter.mp hv
        obtain ⟨w, hw, huw⟩ := (ih u).1 hu
        exact ⟨w, hw, graphBall_step D {w} huw hvu⟩
    · rintro ⟨w, hw, hvw⟩
      exact graphBall_seed_mono D (Finset.singleton_subset_iff.mpr hw) (R + 1) hvw

private theorem expandCells_mem (D : S18.LateData hPT)
    (s : Finset D.geom.Cell) (C : D.geom.Cell) :
    C ∈ D.expandCells s ↔ ∃ C' ∈ s, C ∈ D.expandCells {C'} := by
  constructor
  · intro hC
    rcases Finset.mem_union.mp hC with hC | hC
    · exact ⟨C, hC, Finset.mem_union_left _ (Finset.mem_singleton_self C)⟩
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
      obtain ⟨w, hw, hvw⟩ := (graphBall_mem_seed D _ _ v).1 hv
      obtain ⟨C', hC', hwC'⟩ := Finset.mem_biUnion.mp hw
      refine ⟨C', hC', Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, ?_, hCv⟩)⟩
      exact graphBall_seed_mono D (by
        intro z hz
        have hz' := Finset.mem_singleton.mp hz
        subst z
        exact Finset.mem_biUnion.mpr ⟨C', Finset.mem_singleton_self _, hwC'⟩) _ hvw
  · rintro ⟨C', hC', hC⟩
    rcases Finset.mem_union.mp hC with hC | hC
    · exact Finset.mem_union_left _ ((Finset.mem_singleton.mp hC) ▸ hC')
    · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, ?_, hCv⟩)
      apply graphBall_seed_mono D _ _ hv
      intro w hw
      obtain ⟨c, hc, hwc⟩ := Finset.mem_biUnion.mp hw
      have : c = C' := Finset.mem_singleton.mp hc
      subst c
      exact Finset.mem_biUnion.mpr ⟨C', hC', hwc⟩

private theorem expandCells_singleton_symm (D : S18.LateData hPT)
    (C C' : D.geom.Cell) : C ∈ D.expandCells {C'} → C' ∈ D.expandCells {C} := by
  intro hC
  rcases Finset.mem_union.mp hC with hC | hC
  · have : C = C' := Finset.mem_singleton.mp hC
    subst C'
    exact Finset.mem_union_left _ (Finset.mem_singleton_self C)
  · obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC
    obtain ⟨w, hw, hvw⟩ := (graphBall_mem_seed D _ _ v).1 hv
    have hwC' : C' ∈ D.encoding.events.scope w := by
      simpa only [Finset.singleton_biUnion, ListEvent.incidentEvents, Finset.mem_filter,
        Finset.mem_univ, true_and] using hw
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, ?_, hwC'⟩)
    apply graphBall_seed_mono D _ _ (graphBall_singleton_symm D _ w v hvw)
    intro z hz
    have hz' := Finset.mem_singleton.mp hz
    subst z
    simp only [Finset.singleton_biUnion, ListEvent.incidentEvents, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hCv

private theorem growth_factor_le {n a t : ℕ} (hn : 2 ≤ n) :
    1 + (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1) ≤
      n ^ ((a + 5) * (2 * t + 4) + 3) := by
  have hp : 0 < n ^ (a + 4) := pow_pos (by omega) _
  have hd : n ^ (a + 4) + 1 ≤ n ^ (a + 5) := by
    calc
      _ ≤ n ^ (a + 4) * n := by nlinarith
      _ = _ := (pow_succ n (a + 4)).symm
  have hnp : n + 1 ≤ n ^ 2 := by nlinarith
  let z := (n ^ (a + 4) + 1) ^ (2 * t + 4) * (n + 1)
  have hz : 1 ≤ z := by
    have hh : 0 < (n ^ (a + 4) + 1) ^ (2 * t + 4) := pow_pos (by omega) _
    dsimp [z]
    nlinarith
  calc
    1 + z ≤ n * z := by nlinarith
    _ ≤ n * ((n ^ (a + 5)) ^ (2 * t + 4) * n ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hnp)
    _ = _ := by rw [← pow_mul]; ring

private theorem expanded_card_le (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (s : Finset D.geom.Cell) (e : ℕ)
    (hs : s.card ≤ T.S.n k ^ e) :
    (D.expandCells s).card ≤ T.S.n k ^ (e + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) := by
  calc
    _ ≤ s.card * (1 + (T.S.n k ^ (κ.Ac + 4) + 1) ^
        (2 * D.encoding.Ts + 4) * (T.S.n k + 1)) :=
      Lane_sol_s18_3f.expandCells_card D hD hn s
    _ ≤ T.S.n k ^ e * T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) :=
      Nat.mul_le_mul hs (growth_factor_le hn)
    _ = _ := by rw [← pow_add]; congr 1 <;> omega

private theorem directCells_card_le (D : S18.LateData hPT) (hD : D.Spec) (v : Pos T k) :
    (D.directCells v).card ≤ T.S.n k + 1 := by
  calc
    _ ≤ 1 + (D.externalEarly v).card := by
      exact (Finset.card_union_le _ _).trans (by
        simpa only [Finset.card_singleton] using Nat.add_le_add_left
          (Finset.card_image_le (s := D.externalEarly v)
            (f := fun a => D.geom.cellOf (flipPos v a))) 1)
    _ ≤ T.S.n k + 1 := by
      have h := Finset.card_le_card (Finset.filter_subset
        (fun a : Fin (T.S.n k) => a ∉ PT.tiling.Icoord (D.geom.patchOf v) ∧
          D.geom.classOf (flipPos v a) = none) Finset.univ)
      simpa only [S18.LateData.externalEarly, Finset.card_univ, Fintype.card_fin, add_comm]
        using Nat.add_le_add_left h 1

private theorem late_seed_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (v : Pos T k) :
    ((cubeBall v (10 * D.geom.r)).biUnion D.directCells).card ≤
      T.S.n k ^ (20 * D.geom.r + 2) := by
  have hn2 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  calc
    _ ≤ (cubeBall v (10 * D.geom.r)).card * (T.S.n k + 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun w _ => directCells_card_le D hD w)
    _ ≤ (T.S.n k + 1) ^ (10 * D.geom.r) * (T.S.n k + 1) :=
      Nat.mul_le_mul_right _ (Lane_sol_s18_4b.cubeBall_card v _)
    _ ≤ (T.S.n k ^ 2) ^ (10 * D.geom.r) * T.S.n k ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hn2 _) hn2
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1 <;> omega

/-- Every actual terminal scope has the stated polynomial cell bound. -/
theorem requirementRegion_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (f : S18.TerminalIndex D) :
    (requirementRegion D f).card ≤
      T.S.n k ^ (20 * D.geom.r + 2 + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) := by
  have hn1 : 1 ≤ T.S.n k := by omega
  have hn2 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  have hpow : T.S.n k ^ 2 ≤ T.S.n k ^ (20 * D.geom.r + 2) :=
    Nat.pow_le_pow_right hn1 (by omega)
  have hscope : ∀ v, (D.encoding.events.scope v).card ≤ T.S.n k ^ (20 * D.geom.r + 2) := by
    intro v
    rw [hD.scope_eq]
    exact (directCells_card_le D hD v).trans (hn2.trans hpow)
  cases f with
  | inl f =>
    cases f with
    | inl C =>
      simp only [requirementRegion, Finset.card_singleton]
      exact Nat.one_le_pow _ _ hn1
    | inr v => exact (hscope v).trans (Nat.pow_le_pow_right hn1 (by omega))
  | inr f =>
    cases f with
    | inl v => exact expanded_card_le D hD hn _ _ (hscope v)
    | inr F => exact expanded_card_le D hD hn _ _ (late_seed_card D hD hn _)

/-- The concrete slot, image and tape scopes fit the frozen leaf budget. -/
theorem canonical_scope_bound (hκ : κ.Admissible) (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (hTs : 1 ≤ D.encoding.Ts) (hr : D.geom.r ≤ D.encoding.Ts)
    (hK : κ.Kcell ≤ (T.S.n k : ℝ)) (L : LeafKey D) :
    (((domains D L.1).card + (images D L).card +
      (requirementRegion D L.1).card : ℕ) : ℝ) ≤ scopeBudget D := by
  let n := T.S.n k
  let m := n ^ (κ.Ac + 1)
  have hslots : ∀ C ∈ requirementRegion D L.1, D.geom.nslot C ≤ m := by
    intro C _
    apply (S18.Lane_sol_s18_n5.slot_count_le_uniform hκ D C).trans
    apply Nat.ceil_le.mpr
    rw [Nat.cast_pow, pow_succ]
    simpa [n, mul_comm] using mul_le_mul_of_nonneg_right hK
      (pow_nonneg (Nat.cast_nonneg (T.S.n k)) κ.Ac)
  have hdomEq : domains D L.1 = Lane_sol_s18_3f.testDomains D (requirementRegion D L.1) := by
    ext s
    simp only [mem_domains, Lane_sol_s18_3f.testDomains, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hdom := Lane_sol_s18_3f.testDomains_card D (requirementRegion D L.1) m hslots
  rw [← hdomEq] at hdom
  have him := images_card_le D L
  have hm : 1 ≤ m := Nat.one_le_pow _ _ (by dsimp [n]; omega)
  have hfactor : 2 * m + 1 ≤ n ^ (κ.Ac + 3) := by
    have hn2 : 4 ≤ n ^ 2 := by dsimp [n]; nlinarith
    have hmul := Nat.mul_le_mul_left m hn2
    rw [show κ.Ac + 3 = (κ.Ac + 1) + 2 by omega, pow_add]
    change 2 * m + 1 ≤ m * n ^ 2
    nlinarith
  have hexp : 20 * D.geom.r + 2 + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3 +
      (κ.Ac + 3) ≤ 10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r) := by
    rw [hκ.Ac_eq]
    omega
  have hcount : (domains D L.1).card + (images D L).card +
      (requirementRegion D L.1).card ≤ n ^ (10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r)) := by
    calc
      _ ≤ (requirementRegion D L.1).card * (2 * m + 1) := by nlinarith
      _ ≤ n ^ (20 * D.geom.r + 2 + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) *
          n ^ (κ.Ac + 3) := Nat.mul_le_mul (requirementRegion_card D hD hn L.1) hfactor
      _ = n ^ (20 * D.geom.r + 2 + (κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3 +
          (κ.Ac + 3)) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by dsimp [n]; omega) hexp
  have he : 10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) =
      ((10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r) : ℕ) : ℝ) := by push_cast; ring
  rw [scopeBudget, he, Real.rpow_eq_pow, Real.rpow_natCast]
  exact_mod_cast hcount

private theorem incidentEvents_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (C : D.geom.Cell) :
    (D.encoding.events.incidentEvents C).card ≤ T.S.n k ^ (κ.Ac + 4) + 1 := by
  let d := T.S.n k ^ (κ.Ac + 4)
  have hd := Lane_sol_s18_n4.eventDegreeBound D hD hn
  by_cases h : (D.encoding.events.incidentEvents C).Nonempty
  · obtain ⟨v, hv⟩ := h
    have hsub : D.encoding.events.incidentEvents C ⊆
        insert v (Finset.univ.filter fun w => D.encoding.events.Adjacent v w) := by
      intro w hw
      by_cases heq : w = v
      · exact heq ▸ Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, fun h => heq h.symm, ?_⟩
        apply Finset.not_disjoint_iff.mpr
        exact ⟨C, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hw).2⟩
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hd v) 1))
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

private noncomputable def incomingEvents (D : S18.LateData hPT) (C : D.geom.Cell) :
    Finset (Pos T k) := (D.expandCells {C}).biUnion D.encoding.events.incidentEvents

private theorem incomingEvents_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (C : D.geom.Cell) :
    (incomingEvents D C).card ≤
      T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 5) + 3) := by
  have hd : T.S.n k ^ (κ.Ac + 4) + 1 ≤ T.S.n k ^ (κ.Ac + 5) := by
    have hp : 1 ≤ T.S.n k ^ (κ.Ac + 4) := Nat.one_le_pow _ _ (by omega)
    have hn2 := Nat.mul_le_mul_left (T.S.n k ^ (κ.Ac + 4)) hn
    calc
      _ ≤ T.S.n k ^ (κ.Ac + 4) * T.S.n k := by nlinarith only [hp, hn2]
      _ = _ := (pow_succ (T.S.n k) (κ.Ac + 4)).symm
  have hc := expanded_card_le D hD hn ({C} : Finset D.geom.Cell) 0 (by simp)
  calc
    _ ≤ (D.expandCells {C}).card * (T.S.n k ^ (κ.Ac + 4) + 1) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun c _ => incidentEvents_card D hD hn c)
    _ ≤ T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 4) + 3) *
        T.S.n k ^ (κ.Ac + 5) := Nat.mul_le_mul (by simpa only [zero_add] using hc) hd
    _ = _ := by rw [← pow_add]; congr 1 <;> ring

private theorem incoming_initial (D : S18.LateData hPT)
    (C : D.geom.Cell) (v : Pos T k) (hv : C ∈ D.initialRegion v) :
    v ∈ incomingEvents D C := by
  obtain ⟨C', hC', hCC'⟩ := (expandCells_mem D _ C).1 hv
  exact Finset.mem_biUnion.mpr ⟨C', expandCells_singleton_symm D C C' hCC',
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'⟩⟩

private theorem incoming_scope (D : S18.LateData hPT)
    (C : D.geom.Cell) (v : Pos T k) (hv : C ∈ D.encoding.events.scope v) :
    v ∈ incomingEvents D C :=
  Finset.mem_biUnion.mpr ⟨C, Finset.mem_union_left _ (Finset.mem_singleton_self C),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩

private noncomputable def incomingCenters (D : S18.LateData hPT) (C : D.geom.Cell) :
    Finset (Pos T k) := (incomingEvents D C).biUnion fun v => cubeBall v (10 * D.geom.r)

private theorem incoming_late (D : S18.LateData hPT) (hD : D.Spec)
    (C : D.geom.Cell) (F : S18.LateEvent D) (hF : C ∈ D.lateRegion F) :
    F.2.2.1.1 ∈ incomingCenters D C := by
  obtain ⟨C', hC', hCC'⟩ := (expandCells_mem D _ C).1 hF
  obtain ⟨v, hv, hCv⟩ := Finset.mem_biUnion.mp hC'
  have hvc : v ∈ incomingEvents D C := Finset.mem_biUnion.mpr
    ⟨C', expandCells_singleton_symm D C C' hCC',
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rwa [hD.scope_eq]⟩⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨v, hvc, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simpa only [hammingDist_comm] using (Finset.mem_filter.mp hv).2

private theorem incomingCenters_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 2 ≤ T.S.n k) (C : D.geom.Cell) :
    (incomingCenters D C).card ≤
      T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 5) + 3 + 20 * D.geom.r) := by
  have hn2 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
  calc
    _ ≤ (incomingEvents D C).card * (T.S.n k + 1) ^ (10 * D.geom.r) :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun v _ => Lane_sol_s18_4b.cubeBall_card v _)
    _ ≤ T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 5) + 3) *
        (T.S.n k ^ 2) ^ (10 * D.geom.r) :=
      Nat.mul_le_mul (incomingEvents_card D hD hn C) (Nat.pow_le_pow_left hn2 _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1 <;> omega

/-- Disjoint late classes give only three finite test-index factors per anchor. -/
private theorem lateEvent_anchor_injective (D : S18.LateData hPT) :
    Function.Injective (fun F : S18.LateEvent D => (F.2.2.1.1, F.1, F.2.2.2)) := by
  rintro ⟨kind, j, b, idx⟩ ⟨kind', j', b', idx'⟩ h
  have hb : b.1 = b'.1 := congrArg (fun z => z.1) h
  have hj : j = j' := by
    by_contra hne
    exact Finset.disjoint_left.mp (D.encoding.base.class_disjoint j j' hne) b.2 (hb ▸ b'.2)
  cases hj
  have hbb : b = b' := Subtype.ext hb
  cases hbb
  have hrest : (kind, idx) = (kind', idx') := congrArg Prod.snd h
  cases Prod.mk.inj hrest with
  | intro hkind hidx => cases hkind; cases hidx; rfl

/-- Incoming requirement counts are deterministic, independent of all images and tapes. -/
theorem incidentRequirements_card (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 4 ≤ T.S.n k) (C : D.geom.Cell) :
    (incidentRequirements D C).card ≤
      T.S.n k ^ ((κ.Ac + 5) * (2 * D.encoding.Ts + 5) + 3 + 20 * D.geom.r + 7) := by
  let I := {f : S18.TerminalIndex D // C ∈ requirementRegion D f}
  let J := Unit ⊕ ((incomingEvents D C) ⊕
    ((incomingEvents D C) ⊕ ((incomingCenters D C) × Fin 3 ×
      Fin (T.S.n k + 1) × Fin (T.S.n k + 1) × Fin (T.S.n k))))
  let toJ : I → J := fun f => match f with
    | ⟨.inl (.inl _), _⟩ => .inl ()
    | ⟨.inl (.inr v), hv⟩ => .inr (.inl ⟨v, incoming_scope D C v hv⟩)
    | ⟨.inr (.inl v), hv⟩ => .inr (.inr (.inl ⟨v, incoming_initial D C v hv⟩))
    | ⟨.inr (.inr F), hF⟩ => .inr (.inr (.inr (⟨F.2.2.1.1, incoming_late D hD C F hF⟩,
        F.1, F.2.2.2)))
  have hinj : Function.Injective toJ := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    apply Subtype.ext
    cases f with
    | inl f =>
      cases f with
      | inl c =>
        have hc : C = c := Finset.mem_singleton.mp hf
        subst c
        cases g with
        | inl g =>
          cases g with
          | inl c' => have hc' : C = c' := Finset.mem_singleton.mp hg; subst c'; rfl
          | inr v => cases h
        | inr g => cases g <;> cases h
      | inr v =>
        cases g with
        | inl g =>
          cases g with
          | inl c => cases h
          | inr w =>
            have hvw : v = w := congrArg (fun z : J => match z with
              | .inr (.inl a) => a.1
              | _ => v) h
            cases hvw; rfl
        | inr g => cases g <;> cases h
    | inr f =>
      cases f with
      | inl v =>
        cases g with
        | inl g => cases g <;> cases h
        | inr g =>
          cases g with
          | inl w =>
            have hvw : v = w := congrArg (fun z : J => match z with
              | .inr (.inr (.inl a)) => a.1
              | _ => v) h
            cases hvw; rfl
          | inr F => cases h
      | inr F =>
        cases g with
        | inl g => cases g <;> cases h
        | inr g =>
          cases g with
          | inl v => cases h
          | inr G =>
            have hFG : (F.2.2.1.1, F.1, F.2.2.2) = (G.2.2.1.1, G.1, G.2.2.2) :=
              congrArg (fun z : J => match z with
                | .inr (.inr (.inr a)) => (a.1.1, a.2)
                | _ => (F.2.2.1.1, F.1, F.2.2.2)) h
            exact congrArg (fun a => Sum.inr (Sum.inr a)) (lateEvent_anchor_injective D hFG)
  let e := (κ.Ac + 5) * (2 * D.encoding.Ts + 5) + 3 + 20 * D.geom.r
  let A := T.S.n k ^ e
  have hn1 : 1 ≤ T.S.n k := by omega
  have hA : 1 ≤ A := Nat.one_le_pow _ _ hn1
  have hJ : (incomingEvents D C).card ≤ A :=
    (incomingEvents_card D hD (by omega) C).trans (Nat.pow_le_pow_right hn1 (by dsimp [e]; omega))
  have hB : (incomingCenters D C).card ≤ A := incomingCenters_card D hD (by omega) C
  have hindices : 3 * ((T.S.n k + 1) * ((T.S.n k + 1) * T.S.n k)) ≤ T.S.n k ^ 6 := by
    have hn2 : T.S.n k + 1 ≤ T.S.n k ^ 2 := by nlinarith
    have hm := Nat.mul_le_mul (by omega : 3 ≤ T.S.n k)
      (Nat.mul_le_mul hn2 (Nat.mul_le_mul_right (T.S.n k) hn2))
    nlinarith [hm]
  have hN : 1 ≤ T.S.n k ^ 6 := Nat.one_le_pow _ _ hn1
  have hcount : Fintype.card J ≤ T.S.n k ^ (e + 7) := by
    simp only [J, Fintype.card_sum, Fintype.card_unit, Fintype.card_coe,
      Fintype.card_prod, Fintype.card_fin]
    have hlate : (incomingCenters D C).card * (3 * ((T.S.n k + 1) *
        ((T.S.n k + 1) * T.S.n k))) ≤ A * T.S.n k ^ 6 := Nat.mul_le_mul hB hindices
    have hscale := Nat.mul_le_mul_left (A * T.S.n k ^ 6) hn
    have h1 := Nat.mul_le_mul_left A hN
    have h2 := Nat.mul_le_mul_left (T.S.n k ^ 6) hA
    calc
      _ ≤ 4 * (A * T.S.n k ^ 6) := by nlinarith
      _ ≤ T.S.n k * (A * T.S.n k ^ 6) := by simpa only [mul_comm] using hscale
      _ = _ := by dsimp [A]; rw [← pow_add]; ring
  calc
    _ = Fintype.card I := (Fintype.card_subtype _).symm
    _ ≤ Fintype.card J := Fintype.card_le_of_injective toJ hinj
    _ ≤ _ := hcount

/-- The deterministic incidence count fits the same frozen budget as a leaf scope. -/
theorem canonical_incidence_bound (hκ : κ.Admissible) (D : S18.LateData hPT) (hD : D.Spec)
    (hn : 4 ≤ T.S.n k) (hTs : 1 ≤ D.encoding.Ts) (hr : D.geom.r ≤ D.encoding.Ts)
    (C : D.geom.Cell) : (incidentRequirements D C).card ≤ ⌊scopeBudget D⌋₊ := by
  have hexp : (κ.Ac + 5) * (2 * D.encoding.Ts + 5) + 3 + 20 * D.geom.r + 7 ≤
      10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r) := by rw [hκ.Ac_eq]; omega
  have hcount := (incidentRequirements_card D hD hn C).trans
    (Nat.pow_le_pow_right (by omega) hexp)
  have he : 10 * (((κ.Ac + 4) * D.encoding.Ts + D.geom.r : ℕ) : ℝ) =
      ((10 * ((κ.Ac + 4) * D.encoding.Ts + D.geom.r) : ℕ) : ℝ) := by push_cast; ring
  rw [scopeBudget, he, Real.rpow_eq_pow, Real.rpow_natCast]
  rw [← Nat.cast_pow, Nat.floor_natCast]
  exact hcount

private theorem map_map {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (P : FinLaw A) (f : A → B) (g : B → C) :
    FinLaw.map (FinLaw.map P f) g = FinLaw.map P (fun x => g (f x)) := by
  apply Lane_q_s16_comp1.finlaw_ext
  intro z
  unfold FinLaw.map
  have hterm : ∀ y,
      (if g y = z then ∑ x, if f x = y then P.w x else 0 else 0) =
        ∑ x, if f x = y then (if g (f x) = z then P.w x else 0) else 0 := by
    intro y
    by_cases hg : g y = z
    · simp only [hg, ite_true]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hf : f x = y <;> simp [hf, hg]
    · simp only [hg, ite_false]
      symm
      apply Finset.sum_eq_zero
      intro x hx
      by_cases hf : f x = y <;> simp [hf, hg]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp

private theorem uniform_map_injective {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (s : Finset A) (hs : s.Nonempty)
    (f : A → B) (hf : Function.Injective f) :
    FinLaw.map (FinLaw.uniform s hs) f = FinLaw.uniform (s.image f) (hs.image f) := by
  apply Lane_q_s16_comp1.finlaw_ext
  intro y
  have hc := Finset.card_image_of_injective s hf
  by_cases hy : y ∈ s.image f
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    change (∑ a, if f a = f x then (FinLaw.uniform s hs).w a else 0) = _
    rw [Finset.sum_eq_single x]
    · simp only [FinLaw.uniform, hx, ite_true, hy, hc]
    · intro x' hx' hne
      have h : f x' ≠ f x := fun heq => hne (hf heq)
      simp [h]
    · simp
  · have h : ∀ x ∈ s, f x ≠ y := by
      intro x hx heq
      exact hy (Finset.mem_image.mpr ⟨x, hx, heq⟩)
    change (∑ x, if f x = y then (if x ∈ s then 1 / (s.card : ℝ) else 0) else 0) = _
    change _ = (if y ∈ s.image f then 1 / ((s.image f).card : ℝ) else 0)
    rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hxs : x ∈ s
    · simp [hxs, h x hxs]
    · simp [hxs]

private theorem map_pi {I : Type*} [Fintype I] [DecidableEq I]
    {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    [∀ i, DecidableEq (B i)] (P : ∀ i, FinLaw (A i)) (f : ∀ i, A i → B i) :
    FinLaw.map (FinLaw.pi P) (fun x i => f i (x i)) =
      FinLaw.pi (fun i => FinLaw.map (P i) (f i)) := by
  apply Lane_q_s16_comp1.finlaw_ext
  intro y
  change (∑ x : ∀ i, A i, if (fun i => f i (x i)) = y then ∏ i, (P i).w (x i) else 0) =
    ∏ i, ∑ a, if f i a = y i then (P i).w a else 0
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : (fun i => f i (x i)) = y
  · simp only [if_pos h]
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_pos (congrFun h i)]
  · rw [if_neg h]
    symm
    obtain ⟨i, hi⟩ := not_forall.mp (fun h' => h (funext h'))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private theorem uniform_cond_inter {A : Type*} [Fintype A] [DecidableEq A]
    (s t : Finset A) (hs : s.Nonempty)
    (hp : 0 < ∑ x ∈ t, (FinLaw.uniform s hs).w x) (ht : (s ∩ t).Nonempty) :
    FinLaw.cond (FinLaw.uniform s hs) t hp = FinLaw.uniform (s ∩ t) ht := by
  apply Lane_q_s16_comp1.finlaw_eq_of_const_on_set _ _ (s ∩ t) ht
    ((1 / (s.card : ℝ)) / ∑ x ∈ t, (FinLaw.uniform s hs).w x)
    (1 / ((s ∩ t).card : ℝ))
  · intro y hy
    by_cases hs' : y ∈ s <;> by_cases ht' : y ∈ t <;> simp_all [FinLaw.cond, FinLaw.uniform]
  · intro y hy
    simp only [FinLaw.uniform, if_neg hy]
  · intro y hy
    obtain ⟨hyS, hyT⟩ := Finset.mem_inter.mp hy
    simp [FinLaw.cond, FinLaw.uniform, hyS, hyT]
  · intro y hy
    simp only [FinLaw.uniform, if_pos hy]

abbrev PatchSlot (D : S18.LateData hPT) (i : Fin PT.tiling.m) :=
  Σ C : {C : D.geom.Cell // D.geom.cellPatch C = i}, Fin (D.geom.nslot C.1)
abbrev PatchInjections (D : S18.LateData hPT) :=
  ∀ i : Fin PT.tiling.m, PatchSlot D i ↪ Bin PT.tiling i

noncomputable def decodePools (D : S18.LateData hPT) (x : PatchInjections D) :
    ∀ C, D.fresh.Pool C := fun C s => x (D.geom.cellPatch C) ⟨⟨C, rfl⟩, s⟩

noncomputable def encodePoolValue (D : S18.LateData hPT) (p : ∀ C, D.fresh.Pool C)
    (i : Fin PT.tiling.m) (s : PatchSlot D i) : Bin PT.tiling i :=
  ⟨(p s.1.1 s.2).1, by
    let b : Finset (Fin (T.S.N k)) := (p s.1.1 s.2).1
    have h : b ∈ (PT.tiling.P (D.geom.cellPatch s.1.1)).bins.parts := (p s.1.1 s.2).2
    exact (congrArg (fun j : Fin PT.tiling.m => b ∈ (PT.tiling.P j).bins.parts) s.1.2) ▸ h⟩

noncomputable def encodePools (D : S18.LateData hPT) (p : ∀ C, D.fresh.Pool C)
    (hp : p ∈ permPools D.geom) : PatchInjections D := fun i =>
  ⟨encodePoolValue D p i, by
    intro s t h
    have hinj := (Finset.mem_filter.mp hp).2 s.1.1 t.1.1 s.2 t.2
      (s.1.2.trans t.1.2.symm) (congrArg Subtype.val h)
    have hC : s.1 = t.1 := Subtype.ext hinj.1
    cases s with
    | mk C a =>
      cases t with
      | mk C' a' =>
        dsimp at hC
        cases hC
        have ha : a = a' := Fin.ext hinj.2
        cases ha
        rfl⟩

private theorem encodePoolValue_decode (D : S18.LateData hPT) (x : PatchInjections D)
    (i : Fin PT.tiling.m) (s : PatchSlot D i) :
    encodePoolValue D (decodePools D x) i s = x i s := by
  rcases s with ⟨⟨C, hC⟩, a⟩
  cases hC
  apply Subtype.ext
  rfl

theorem decodePools_perm (D : S18.LateData hPT) (x : PatchInjections D) :
    decodePools D x ∈ permPools D.geom := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro C C' s s' hpatch hval
  have heq : x (D.geom.cellPatch C) ⟨⟨C, rfl⟩, s⟩ =
      x (D.geom.cellPatch C) ⟨⟨C', hpatch.symm⟩, s'⟩ := by
    have h : encodePoolValue D (decodePools D x) (D.geom.cellPatch C) ⟨⟨C, rfl⟩, s⟩ =
        encodePoolValue D (decodePools D x) (D.geom.cellPatch C) ⟨⟨C', hpatch.symm⟩, s'⟩ :=
      Subtype.ext hval
    simpa only [encodePoolValue_decode] using h
  have hs := (x (D.geom.cellPatch C)).injective heq
  have hC : C = C' := congrArg (fun a : PatchSlot D (D.geom.cellPatch C) => a.1.1) hs
  subst C'
  have hss : s = s' := eq_of_heq (Sigma.mk.inj hs).2
  exact ⟨rfl, congrArg Fin.val hss⟩

theorem decode_encodePools (D : S18.LateData hPT) (p : ∀ C, D.fresh.Pool C)
    (hp : p ∈ permPools D.geom) : decodePools D (encodePools D p hp) = p := by
  funext C s
  apply Subtype.ext
  rfl

theorem encode_decodePools (D : S18.LateData hPT) (x : PatchInjections D) :
    encodePools D (decodePools D x) (decodePools_perm D x) = x := by
  funext i
  apply Function.Embedding.ext
  rintro ⟨⟨C, hC⟩, s⟩
  cases hC
  apply Subtype.ext
  rfl

theorem decodePools_injective (D : S18.LateData hPT) : Function.Injective (decodePools D) := by
  intro x y h
  have hx := encode_decodePools D x
  have hy := encode_decodePools D y
  rw [← hx, ← hy]
  congr 1

noncomputable def forcingPatchSlots (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (i : Fin PT.tiling.m) : Finset (PatchSlot D i) :=
  Finset.univ.filter fun s => s.1.1 ∈ region

noncomputable def forcePatchInjections (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (target x : PatchInjections D) : PatchInjections D :=
  fun i => Lane_sol_s18_n4.forceInjectionPins (target i) (forcingPatchSlots D region i).toList (x i)

noncomputable def forcePools (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) (ht : target ∈ permPools D.geom)
    (p : ∀ C, D.fresh.Pool C) : ∀ C, D.fresh.Pool C :=
  if hp : p ∈ permPools D.geom then
    decodePools D (forcePatchInjections D region (encodePools D target ht) (encodePools D p hp))
  else fun C => if C ∈ region then target C else p C

/-- Swaps are extended to zero-mass, off-support inputs by a local overwrite. -/
theorem forcePools_prescribed (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) (ht : target ∈ permPools D.geom)
    (p : ∀ C, D.fresh.Pool C) (C : D.geom.Cell) (hC : C ∈ region) :
    forcePools D region target ht p C = target C := by
  funext s
  by_cases hp : p ∈ permPools D.geom
  · simp only [forcePools, dif_pos hp, decodePools, forcePatchInjections]
    exact Lane_sol_s18_n4.forceInjectionPins_image _ _ _
      (by simp [forcingPatchSlots, hC]) _
  · simp [forcePools, hp, hC]

/-- An occurring image outside the forcing's domain and image sets is fixed. -/
theorem forcePools_preserves (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) (ht : target ∈ permPools D.geom)
    (p : ∀ C, D.fresh.Pool C) (C : D.geom.Cell) (s : Fin (D.geom.nslot C))
    (hC : C ∉ region)
    (himage : ∀ C' ∈ region, ∀ s' : Fin (D.geom.nslot C'),
      D.geom.cellPatch C' = D.geom.cellPatch C → (p C s).1 ≠ (target C' s').1) :
    forcePools D region target ht p C s = p C s := by
  by_cases hp : p ∈ permPools D.geom
  · simp only [forcePools, dif_pos hp, decodePools, forcePatchInjections]
    apply Lane_sol_s18_n4.forceInjectionPins_nonneighbor
    · simpa only [Finset.mem_toList, forcingPatchSlots, Finset.mem_filter,
        Finset.mem_univ, true_and] using hC
    · intro s' hs'
      have hR : s'.1.1 ∈ region := (Finset.mem_filter.mp (Finset.mem_toList.mp hs')).2
      intro heq
      exact himage s'.1.1 hR s'.2 s'.1.2 (congrArg Subtype.val heq)
    · apply Subtype.ext; rfl
  · simp [forcePools, hp, hC]

noncomputable def prescribedPools (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) : Finset (∀ C, D.fresh.Pool C) :=
  Finset.univ.filter fun p => ∀ C ∈ region, p C = target C

private noncomputable def pinnedPatchProduct (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (target : PatchInjections D) : Finset (PatchInjections D) :=
  Finset.univ.filter fun x => ∀ i, x i ∈ Lane_sol_s18_n4.injectionPinSet
    (target i) (forcingPatchSlots D region i)

private theorem pinnedPatchProduct_nonempty (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (target : PatchInjections D) :
    (pinnedPatchProduct D region target).Nonempty := by
  refine ⟨target, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i
  simp [Lane_sol_s18_n4.injectionPinSet]

private theorem decodePools_univ_image (D : S18.LateData hPT) :
    (Finset.univ : Finset (PatchInjections D)).image (decodePools D) = permPools D.geom := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact decodePools_perm D x
  · intro hp
    exact Finset.mem_image.mpr ⟨encodePools D p hp, Finset.mem_univ _, decode_encodePools D p hp⟩

private theorem decodePools_pinned_image (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (target : ∀ C, D.fresh.Pool C)
    (ht : target ∈ permPools D.geom) :
    (pinnedPatchProduct D region (encodePools D target ht)).image (decodePools D) =
      permPools D.geom ∩ prescribedPools D region target := by
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_inter.mpr ⟨decodePools_perm D x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro C hC
    funext s
    have hx' := (Finset.mem_filter.mp hx).2 (D.geom.cellPatch C)
    have h := (Lane_sol_s18_n4.mem_injectionPinSet _ _ _).1 hx'
      (⟨⟨C, rfl⟩, s⟩ : PatchSlot D (D.geom.cellPatch C))
      (by simp [forcingPatchSlots, hC])
    exact h
  · intro hp
    obtain ⟨hp, hpres⟩ := Finset.mem_inter.mp hp
    refine Finset.mem_image.mpr ⟨encodePools D p hp, ?_, decode_encodePools D p hp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i
    apply (Lane_sol_s18_n4.mem_injectionPinSet _ _ _).2
    intro s hs
    have hC := (Finset.mem_filter.mp hs).2
    have heq := (Finset.mem_filter.mp hpres).2 s.1.1 hC
    apply Subtype.ext
    exact congrArg (fun q : D.fresh.Pool s.1.1 => (q s.2).1) heq

set_option maxHeartbeats 800000 in
private theorem forcePatch_uniform (D : S18.LateData hPT)
    (region : Finset D.geom.Cell) (target : PatchInjections D) :
    FinLaw.map (FinLaw.uniform Finset.univ ⟨target, Finset.mem_univ _⟩)
      (forcePatchInjections D region target) =
      FinLaw.uniform (pinnedPatchProduct D region target)
        (pinnedPatchProduct_nonempty D region target) := by
  have hall : FinLaw.uniform (Finset.univ : Finset (PatchInjections D))
      ⟨target, Finset.mem_univ _⟩ =
      FinLaw.pi (fun i => FinLaw.uniform Finset.univ ⟨target i, Finset.mem_univ _⟩) := by
    convert S18.Lane_sol_s18_n5.uniform_pi_sets
      (fun i : Fin PT.tiling.m => (Finset.univ : Finset (PatchSlot D i ↪ Bin PT.tiling i)))
      (fun i => ⟨target i, Finset.mem_univ _⟩) using 1 <;> simp
  rw [hall]
  change FinLaw.map (FinLaw.pi (fun i => FinLaw.uniform Finset.univ ⟨target i, Finset.mem_univ _⟩))
    (fun x i => Lane_sol_s18_n4.forceInjectionPins (target i)
      (forcingPatchSlots D region i).toList (x i)) = _
  rw [map_pi]
  have hstep : ∀ i, FinLaw.map
      (FinLaw.uniform (Finset.univ : Finset (PatchSlot D i ↪ Bin PT.tiling i))
        ⟨target i, Finset.mem_univ _⟩)
      (Lane_sol_s18_n4.forceInjectionPins (target i) (forcingPatchSlots D region i).toList) =
      FinLaw.uniform (Lane_sol_s18_n4.injectionPinSet (target i) (forcingPatchSlots D region i))
        (Lane_sol_s18_n4.injectionPinSet_nonempty _ _) := by
    intro i
    have h := Lane_sol_s18_n4.forceInjectionPins_uniform (target i)
      (forcingPatchSlots D region i).toList ∅
    have hempty : Lane_sol_s18_n4.injectionPinSet (target i) ∅ = Finset.univ := by
      ext x
      simp only [Lane_sol_s18_n4.injectionPinSet, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
    simpa only [hempty, Finset.toList_toFinset, Finset.empty_union] using h
  simp_rw [hstep]
  symm
  have h := S18.Lane_sol_s18_n5.uniform_pi_sets
    (fun i : Fin PT.tiling.m => Lane_sol_s18_n4.injectionPinSet
      (target i) (forcingPatchSlots D region i))
    (fun i => Lane_sol_s18_n4.injectionPinSet_nonempty (target i) (forcingPatchSlots D region i))
  convert h using 1
  congr 1
  ext x
  simp only [pinnedPatchProduct, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The total pool swap map has the actual pool law conditioned on all consulted images. -/
theorem forcePools_conditional (D : S18.LateData hPT) (region : Finset D.geom.Cell)
    (target : ∀ C, D.fresh.Pool C) (ht : target ∈ permPools D.geom)
    (hp : 0 < ∑ p ∈ prescribedPools D region target, D.encoding.poolLaw.w p) :
    FinLaw.map D.encoding.poolLaw (forcePools D region target ht) =
      FinLaw.cond D.encoding.poolLaw (prescribedPools D region target) hp := by
  let z := encodePools D target ht
  let U := FinLaw.uniform (Finset.univ : Finset (PatchInjections D)) ⟨z, Finset.mem_univ _⟩
  have hdecode : FinLaw.map U (decodePools D) = D.encoding.poolLaw := by
    have he := uniform_map_injective (Finset.univ : Finset (PatchInjections D))
      ⟨z, Finset.mem_univ _⟩ (decodePools D) (decodePools_injective D)
    apply he.trans
    change FinLaw.uniform _ _ = FinLaw.uniform (permPools D.geom) D.encoding.pools_nonempty
    congr 1
    exact decodePools_univ_image D
  have hfun : (fun x => forcePools D region target ht (decodePools D x)) =
      fun x => decodePools D (forcePatchInjections D region z x) := by
    funext x
    dsimp [z]
    simp only [forcePools, dif_pos (decodePools_perm D x), encode_decodePools]
  have hnonempty : (permPools D.geom ∩ prescribedPools D region target).Nonempty := by
    refine ⟨target, Finset.mem_inter.mpr ⟨ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩⟩
    exact fun _ _ => rfl
  calc
    _ = FinLaw.map (FinLaw.map U (decodePools D)) (forcePools D region target ht) := by rw [hdecode]
    _ = FinLaw.map U (fun x => decodePools D (forcePatchInjections D region z x)) := by
      rw [map_map, hfun]
    _ = FinLaw.map (FinLaw.map U (forcePatchInjections D region z)) (decodePools D) :=
      (map_map _ _ _).symm
    _ = FinLaw.map (FinLaw.uniform (pinnedPatchProduct D region z)
        (pinnedPatchProduct_nonempty D region z)) (decodePools D) := by rw [forcePatch_uniform]
    _ = FinLaw.uniform (permPools D.geom ∩ prescribedPools D region target) hnonempty := by
      rw [uniform_map_injective _ _ _ (decodePools_injective D)]
      congr 1
      exact decodePools_pinned_image D region target ht
    _ = _ := (uniform_cond_inter _ _ D.encoding.pools_nonempty hp hnonempty).symm

private theorem kernel_push_weight {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (K : A → FinLaw B) (b : B) :
    (FinLaw.map (FinLaw.bind P K) Prod.snd).w b = ∑ a, P.w a * (K a).w b := by
  change (∑ z : A × B, if z.2 = b then P.w z.1 * (K z.1).w z.2 else 0) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  simp

noncomputable def overwriteTapes {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} (region : Finset I) (old new : ∀ i, A i) : ∀ i, A i :=
  fun i => if i ∈ region then new i else old i

private theorem overwriteTapes_twice {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} (region : Finset I) (t u : ∀ i, A i) :
    overwriteTapes region (overwriteTapes region t u) (overwriteTapes region u t) = t := by
  funext i
  by_cases hi : i ∈ region <;> simp [overwriteTapes, hi]

private noncomputable def tapeSwap {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} (region : Finset I) : ((∀ i, A i) × (∀ i, A i)) ≃
      ((∀ i, A i) × (∀ i, A i)) where
  toFun z := (overwriteTapes region z.1 z.2, overwriteTapes region z.2 z.1)
  invFun z := (overwriteTapes region z.1 z.2, overwriteTapes region z.2 z.1)
  left_inv z := Prod.ext (overwriteTapes_twice region z.1 z.2) (overwriteTapes_twice region z.2 z.1)
  right_inv z := Prod.ext (overwriteTapes_twice region z.1 z.2) (overwriteTapes_twice region z.2 z.1)

set_option maxHeartbeats 800000 in
/-- Conditioning a local tape event and replacing only its consulted tapes
has exactly the conditional tape law. The untouched tapes keep their original law. -/
theorem overwriteTapes_conditional {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (P : ∀ i, FinLaw (A i)) (region : Finset I) (event : Finset (∀ i, A i))
    (hlocal : ∀ t u, (∀ i ∈ region, t i = u i) → (t ∈ event ↔ u ∈ event))
    (hp : 0 < ∑ t ∈ event, (FinLaw.pi P).w t) :
    FinLaw.map (FinLaw.bind (FinLaw.pi P) (fun t =>
      FinLaw.map (FinLaw.cond (FinLaw.pi P) event hp) (overwriteTapes region t))) Prod.snd =
      FinLaw.cond (FinLaw.pi P) event hp := by
  let Q := FinLaw.pi P
  let Z := ∑ t ∈ event, Q.w t
  have hprod : ∀ t u,
      Q.w (overwriteTapes region t u) * Q.w (overwriteTapes region u t) = Q.w t * Q.w u := by
    intro t u
    change (∏ i, (P i).w (overwriteTapes region t u i)) *
      (∏ i, (P i).w (overwriteTapes region u t i)) =
      (∏ i, (P i).w (t i)) * (∏ i, (P i).w (u i))
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : i ∈ region <;> simp [overwriteTapes, h, mul_comm]
  have hevent : ∀ t u, overwriteTapes region u t ∈ event ↔ t ∈ event := by
    intro t u
    apply hlocal
    intro i hi
    simp [overwriteTapes, hi]
  apply Lane_q_s16_comp1.finlaw_ext
  intro y
  rw [kernel_push_weight]
  change (∑ t, Q.w t * ∑ u, if overwriteTapes region t u = y then
      (FinLaw.cond Q event hp).w u else 0) = (FinLaw.cond Q event hp).w y
  simp_rw [Finset.mul_sum]
  let f := fun z : (∀ i, A i) × (∀ i, A i) =>
    Q.w z.1 * (if overwriteTapes region z.1 z.2 = y then
      (FinLaw.cond Q event hp).w z.2 else 0)
  change (∑ t, ∑ u, f (t, u)) = _
  rw [← Fintype.sum_prod_type f]
  rw [← (tapeSwap region).sum_comp f]
  have hterm : ∀ z, f (tapeSwap region z) =
      (if z.1 = y then (FinLaw.cond Q event hp).w z.1 else 0) * Q.w z.2 := by
    rintro ⟨t, u⟩
    simp only [f, tapeSwap, Equiv.coe_fn_mk, overwriteTapes_twice]
    by_cases ht : t = y
    · subst y
      by_cases hE : t ∈ event
      · simp only [ite_true, FinLaw.cond, hevent, hE]
        rw [← mul_div_assoc, hprod]
        ring
      · simp [FinLaw.cond, hevent, hE]
    · simp [ht]
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, Q.sum_one, mul_one]
  simp

private theorem product_cond_mass {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (s : Finset A) (t : Finset B) :
    (∑ z ∈ Finset.univ.filter (fun z : A × B => z.1 ∈ s ∧ z.2 ∈ t),
      (FinLaw.bind P (fun _ => Q)).w z) = (∑ a ∈ s, P.w a) * (∑ b ∈ t, Q.w b) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hterm : ∀ a b, (if a ∈ s ∧ b ∈ t then P.w a * Q.w b else 0) =
      (if a ∈ s then P.w a else 0) * (if b ∈ t then Q.w b else 0) := by
    intro a b
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;> simp [ha, hb]
  change (∑ a, ∑ b, if a ∈ s ∧ b ∈ t then P.w a * Q.w b else 0) = _
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  simp [Finset.sum_ite_mem]

private theorem product_cond {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (s : Finset A) (t : Finset B)
    (hs : 0 < ∑ a ∈ s, P.w a) (ht : 0 < ∑ b ∈ t, Q.w b)
    (hp : 0 < ∑ z ∈ Finset.univ.filter (fun z : A × B => z.1 ∈ s ∧ z.2 ∈ t),
      (FinLaw.bind P (fun _ => Q)).w z) :
    FinLaw.cond (FinLaw.bind P (fun _ => Q))
      (Finset.univ.filter fun z : A × B => z.1 ∈ s ∧ z.2 ∈ t) hp =
        FinLaw.bind (FinLaw.cond P s hs) (fun _ => FinLaw.cond Q t ht) := by
  apply Lane_q_s16_comp1.finlaw_ext
  rintro ⟨a, b⟩
  simp only [FinLaw.cond]
  rw [product_cond_mass]
  simp only [FinLaw.bind, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;>
    simp [ha, hb, div_mul_div_comm]

private theorem product_kernel_push {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (P : FinLaw A) (Q : FinLaw B)
    (f : A → A) (K : B → FinLaw B) :
    FinLaw.map (FinLaw.bind (FinLaw.bind P (fun _ => Q))
      (fun x => FinLaw.map (K x.2) (fun u => (f x.1, u)))) Prod.snd =
        FinLaw.bind (FinLaw.map P f) (fun _ => FinLaw.map (FinLaw.bind Q K) Prod.snd) := by
  have hmk : ∀ a b y, (FinLaw.map (K b) (fun u => (f a, u))).w y =
      if f a = y.1 then (K b).w y.2 else 0 := by
    intro a b y
    change (∑ u, if (f a, u) = y then (K b).w u else 0) = _
    rw [Finset.sum_eq_single y.2]
    · by_cases h : f a = y.1 <;> simp [Prod.ext_iff, h]
    · intro u hu hne
      have h : (f a, u) ≠ y := fun heq => hne (congrArg Prod.snd heq)
      simp [h]
    · simp
  apply Lane_q_s16_comp1.finlaw_ext
  rintro ⟨a', b'⟩
  rw [kernel_push_weight]
  simp_rw [hmk]
  rw [Fintype.sum_prod_type]
  change (∑ a, ∑ b, (P.w a * Q.w b) *
      (if f a = a' then (K b).w b' else 0)) = _
  have hterm : ∀ a b, (P.w a * Q.w b) * (if f a = a' then (K b).w b' else 0) =
      (if f a = a' then P.w a else 0) * (Q.w b * (K b).w b') := by
    intro a b
    by_cases h : f a = a' <;> simp [h, mul_assoc]
  simp_rw [hterm, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  change _ = (FinLaw.map P f).w a' * (FinLaw.map (FinLaw.bind Q K) Prod.snd).w b'
  rw [kernel_push_weight]
  rfl

private theorem positive_map_preimage {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (P : FinLaw A) (f : A → B) (y : B)
    (hy : 0 < (FinLaw.map P f).w y) : ∃ x, f x = y := by
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hy)
  by_cases h : f x = y
  · exact ⟨x, h⟩
  · exact False.elim (hx (by simp [h]))

private theorem occurring_image (D : S18.LateData hPT) (δ : ℝ)
    (L : LeafKey D) (x : D.encoding.InitInput) (hx : x ∈ leaf D δ L)
    (C : D.geom.Cell) (hC : C ∈ requirementRegion D L.1) (s : Fin (D.geom.nslot C)) :
    (⟨D.geom.cellPatch C, x.1 C s⟩ : Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) ∈
      images D L := by
  have hpin := ((mem_leaf D δ L x).1 hx).1
  apply Finset.mem_image.mpr
  refine ⟨⟨⟨C, hC⟩, s⟩, Finset.mem_univ _, ?_⟩
  have heq := congrArg (fun p : PoolSlice D L.1 => p ⟨C, hC⟩ s) hpin
  exact congrArg (Sigma.mk (D.geom.cellPatch C)) heq.symm

/-- Concrete swaps and local tape conditioning force each positive canonical
leaf, including preservation for inputs outside permutation support. -/
theorem canonical_leaf_forcing (D : S18.LateData hPT) (δ : ℝ)
    (hlate : ∀ F x x',
      (∀ C ∈ D.lateRegion F, x.1 C = x'.1 C ∧ x.2 C = x'.2 C) →
      D.pLate F x = D.pLate F x')
    (L : LeafKey D) (hpos : 0 < ∑ x ∈ leaf D δ L, D.encoding.permLaw.w x) :
    ∃ force : D.encoding.InitInput → FinLaw D.encoding.InitInput,
      FinLaw.map (FinLaw.bind D.encoding.permLaw force) Prod.snd =
        FinLaw.cond D.encoding.permLaw (leaf D δ L) hpos ∧
      ∀ x y, 0 < (force x).w y → ∀ L', ¬ adjacent D L L' →
        x ∈ leaf D δ L' → y ∈ leaf D δ L' := by
  obtain ⟨target, htargetLeaf, htargetPos, htargetPerm⟩ := positive_leaf_representative D δ L hpos
  have htarget := ((mem_leaf D δ L target).1 htargetLeaf).1
  let R := requirementRegion D L.1
  let S := poolSliceSet D L
  let E := tapeSliceSet D δ L target
  let P := D.encoding.poolLaw
  let Q := tapeLaw D.fresh D.encoding.Ts
  have hS : S = prescribedPools D R target.1 := by
    ext p
    change p ∈ poolSliceSet D L ↔ p ∈ prescribedPools D R target.1
    simp only [poolSliceSet, prescribedPools, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp C hC
      exact (congrFun hp ⟨C, hC⟩).trans (congrFun htarget ⟨C, hC⟩).symm
    · intro hp
      funext C
      exact (hp C.1 C.2).trans (congrFun htarget C)
  have hrectangle : leaf D δ L = Finset.univ.filter
      (fun x : D.encoding.InitInput => x.1 ∈ S ∧ x.2 ∈ E) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact leaf_factorization D δ hlate L target htarget x
  have hmass : (∑ p ∈ S, P.w p) * (∑ t ∈ E, Q.w t) =
      ∑ x ∈ leaf D δ L, D.encoding.permLaw.w x := by
    rw [hrectangle]
    exact (product_cond_mass P Q S E).symm
  have hPnonneg : 0 ≤ ∑ p ∈ S, P.w p := Finset.sum_nonneg (fun p _ => P.nonneg p)
  have hQnonneg : 0 ≤ ∑ t ∈ E, Q.w t := Finset.sum_nonneg (fun t _ => Q.nonneg t)
  have hPpos : 0 < ∑ p ∈ S, P.w p := by nlinarith [hpos, hmass]
  have hQpos : 0 < ∑ t ∈ E, Q.w t := by nlinarith [hpos, hmass]
  let Kt := fun t => FinLaw.map (FinLaw.cond Q E hQpos) (overwriteTapes R t)
  let fp := forcePools D R target.1 htargetPerm
  let force := fun x : D.encoding.InitInput => FinLaw.map (Kt x.2) (fun u => (fp x.1, u))
  have hpool : FinLaw.map P fp = FinLaw.cond P S hPpos := by
    dsimp [fp]
    have hp' : 0 < ∑ p ∈ prescribedPools D R target.1, D.encoding.poolLaw.w p := by
      simpa only [← hS] using hPpos
    simpa only [← hS] using forcePools_conditional D R target.1 htargetPerm hp'
  have htape : FinLaw.map (FinLaw.bind Q Kt) Prod.snd = FinLaw.cond Q E hQpos := by
    apply overwriteTapes_conditional
    intro t u htu
    exact tape_slice_local D δ hlate L target t u htu
  refine ⟨force, ?_, ?_⟩
  · have hpRect : 0 < ∑ x ∈ Finset.univ.filter
        (fun x : D.encoding.InitInput => x.1 ∈ S ∧ x.2 ∈ E), D.encoding.permLaw.w x := by
      rwa [← hrectangle]
    have hc := product_cond P Q S E hPpos hQpos hpRect
    change FinLaw.map (FinLaw.bind (FinLaw.bind P (fun _ => Q)) force) Prod.snd = _
    rw [product_kernel_push, hpool, htape]
    rw [← hc]
    congr 1
    exact hrectangle.symm
  · intro x y hxy L' hnon hx
    obtain ⟨u, hu⟩ := positive_map_preimage (Kt x.2) (fun u => (fp x.1, u)) y hxy
    have hut : 0 < (Kt x.2).w u := by
      have hy := congrArg (fun z => (force x).w z) hu
      rw [← hy] at hxy
      dsimp [force] at hxy
      have hw : (FinLaw.map (Kt x.2) (fun u => (fp x.1, u))).w (fp x.1, u) =
          (Kt x.2).w u := by
        change (∑ v, if (fp x.1, v) = (fp x.1, u) then (Kt x.2).w v else 0) = _
        rw [Finset.sum_eq_single u]
        · simp
        · intro v hv hne
          have h : (fp x.1, v) ≠ (fp x.1, u) := fun h => hne (congrArg Prod.snd h)
          simp [h]
        · intro hno
          exact False.elim (hno (Finset.mem_univ u))
      rwa [hw] at hxy
    obtain ⟨t, ht⟩ := positive_map_preimage (FinLaw.cond Q E hQpos) (overwriteTapes R x.2) u hut
    have hdis : Disjoint (domains D L.1) (domains D L'.1) ∧
        Disjoint (images D L) (images D L') ∧ Disjoint R (requirementRegion D L'.1) := by
      simpa only [adjacent, not_or, not_not, R] using hnon
    apply (leaf_depends_on D δ hlate L' x y ?_ ?_).mp hx
    · intro s hs
      have hsR := (mem_domains D L'.1 s).1 hs
      have hsOut : s.1 ∉ R := fun h => Finset.disjoint_left.mp hdis.2.2 h hsR
      have hyPool : y.1 = fp x.1 := (congrArg Prod.fst hu).symm
      rw [hyPool]
      symm
      apply forcePools_preserves D R target.1 htargetPerm x.1 s.1 s.2 hsOut
      intro C hC a hpatch heq
      have hown := occurring_image D δ L target htargetLeaf C hC a
      have hother := occurring_image D δ L' x hx s.1 hsR s.2
      have himEq : (⟨D.geom.cellPatch C, target.1 C a⟩ :
          Sigma fun i : Fin PT.tiling.m => Bin PT.tiling i) =
        ⟨D.geom.cellPatch s.1, x.1 s.1 s.2⟩ := by
        apply Sigma.ext hpatch
        exact (Subtype.heq_iff_coe_eq (by
          intro B
          change B ∈ (PT.tiling.P (D.geom.cellPatch C)).bins.parts ↔
            B ∈ (PT.tiling.P (D.geom.cellPatch s.1)).bins.parts
          rw [hpatch])).mpr heq.symm
      exact Finset.disjoint_left.mp hdis.2.1 hown (himEq.symm ▸ hother)
    · intro C hC
      have hOut : C ∉ R := fun h => Finset.disjoint_left.mp hdis.2.2 h hC
      have hyTape : y.2 = overwriteTapes R x.2 t :=
        (congrArg Prod.snd hu).symm.trans ht.symm
      rw [hyTape]
      simp [overwriteTapes, hOut]

/-- The canonical leaf constructor has no remaining analytic inputs beyond
its already proved terminal locality and deterministic geometric counts. -/
theorem canonicalLeafInputs_of_bounds (hκ : κ.Admissible) (D : S18.LateData hPT)
    (hD : D.Spec) (H : S18.TransitionData D) (δ : ℝ)
    (hn : 4 ≤ T.S.n k) (hTs : 1 ≤ D.encoding.Ts) (hr : D.geom.r ≤ D.encoding.Ts)
    (hK : κ.Kcell ≤ (T.S.n k : ℝ)) : Nonempty (CanonicalLeafInputs D δ) := by
  let K := fun L hL => Classical.choose
    (canonical_leaf_forcing D δ (late_probability_local D hD H) L hL)
  have hKspec := fun L hL => Classical.choose_spec
    (canonical_leaf_forcing D δ (late_probability_local D hD H) L hL)
  exact ⟨{
    scope := canonical_scope_bound hκ D hD (by omega) hTs hr hK
    incidence := canonical_incidence_bound hκ D hD hn hTs hr
    force := K
    pushforward := fun L hL => (hKspec L hL).1
    preserves := fun L hL => (hKspec L hL).2
  }⟩

end HypercubeRamsey.Lane_sol_s18_3e
