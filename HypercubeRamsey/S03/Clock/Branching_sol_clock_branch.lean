import HypercubeRamsey.S03.Clock.Paths
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_clock_branch

open scoped BigOperators
open Classical

noncomputable section

private theorem weight_split {E : Type*} [Fintype E] [DecidableEq E]
    {A : E → Type*} [∀ e, Fintype (A e)] (P : ∀ e, FinProb (A e))
    (s : Finset E) (x : ∀ e, A e) :
    (∏ e, (P e).w (x e)) =
      (∏ e : {e // e ∈ s}, (P e.1).w (x e.1)) *
      (∏ e : {e // e ∉ s}, (P e.1).w (x e.1)) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e => e ∈ s)]
  congr 1
  · have hs : Finset.univ.filter (fun e => e ∈ s) = s := by ext e; simp
    rw [hs]
    exact (Finset.prod_coe_sort s (fun e => (P e).w (x e))).symm
  · rw [← Finset.prod_coe_sort]
    symm
    exact Fintype.prod_equiv
      (Equiv.subtypeEquivRight (by intro e; simp : ∀ e, e ∉ s ↔ e ∈ Finset.univ.filter (fun e => e ∉ s)))
      _ _ (by intro e; rfl)

theorem expect_split {E : Type*} [Fintype E] [DecidableEq E]
    {A : E → Type*} [∀ e, Fintype (A e)] (P : ∀ e, FinProb (A e))
    (s : Finset E) (f : (∀ e, A e) → ℝ) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun e : {e // e ∈ s} => P e.1)).expect (fun a =>
        (FinProb.pi (fun e : {e // e ∉ s} => P e.1)).expect (fun b =>
          f ((Equiv.piEquivPiSubtypeProd (fun e => e ∈ s) A).symm (a, b)))) := by
  classical
  let eqv := Equiv.piEquivPiSubtypeProd (fun e => e ∈ s) A
  unfold FinProb.expect
  rw [← Equiv.sum_comp eqv.symm, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  change (∏ e, (P e).w (eqv.symm (a, b) e)) * _ = _
  rw [weight_split P s]
  have hl (e : {e // e ∈ s}) : eqv.symm (a, b) e.1 = a e := by
    simp [eqv, Equiv.piEquivPiSubtypeProd]
  have hr (e : {e // e ∉ s}) : eqv.symm (a, b) e.1 = b e := by
    simp [eqv, Equiv.piEquivPiSubtypeProd, e.2]
  simp_rw [hl, hr]
  exact mul_assoc _ _ _

noncomputable def mix {E : Type*} [DecidableEq E] {A : E → Type*}
    (s : Finset E) (a b : ∀ e, A e) : ∀ e, A e := fun e => if e ∈ s then a e else b e

theorem expect_resample {E : Type*} [Fintype E] [DecidableEq E]
    {A : E → Type*} [∀ e, Fintype (A e)] (P : ∀ e, FinProb (A e))
    (s : Finset E) (f : (∀ e, A e) → ℝ) :
    (FinProb.pi P).expect f =
      (FinProb.pi P).expect (fun a => (FinProb.pi P).expect (fun b => f (mix s a b))) := by
  classical
  let eqv := Equiv.piEquivPiSubtypeProd (fun e => e ∈ s) A
  let Ps := FinProb.pi (fun e : {e // e ∈ s} => P e.1)
  let Pc := FinProb.pi (fun e : {e // e ∉ s} => P e.1)
  rw [expect_split P s f, expect_split P s]
  change Ps.expect (fun a => Pc.expect (fun b => f (eqv.symm (a, b)))) =
    Ps.expect (fun a => Pc.expect (fun b =>
      (FinProb.pi P).expect (fun z => f (mix s (eqv.symm (a, b)) z))))
  congr 1
  funext a
  have hb (b) : (FinProb.pi P).expect (fun z => f (mix s (eqv.symm (a, b)) z)) =
      Pc.expect (fun d => f (eqv.symm (a, d))) := by
    rw [expect_split P s]
    change Ps.expect (fun c => Pc.expect (fun d =>
      f (mix s (eqv.symm (a, b)) (eqv.symm (c, d))))) = Pc.expect (fun d => f (eqv.symm (a, d)))
    have he (c) (d) : mix s (eqv.symm (a, b)) (eqv.symm (c, d)) = eqv.symm (a, d) := by
      funext e
      by_cases h : e ∈ s <;> simp [mix, eqv, Equiv.piEquivPiSubtypeProd, h]
    simp_rw [he]
    exact FinProb.expect_const _ _
  have hfun : (fun b => (FinProb.pi P).expect (fun z => f (mix s (eqv.symm (a, b)) z))) =
      fun _ => Pc.expect (fun d => f (eqv.symm (a, d))) := funext hb
  rw [hfun, FinProb.expect_const]

theorem expect_prod {E : Type*} [Fintype E] [DecidableEq E]
    {A : E → Type*} [∀ e, Fintype (A e)] (P : ∀ e, FinProb (A e))
    (f : ∀ e, A e → ℝ) :
    (FinProb.pi P).expect (fun x => ∏ e, f e (x e)) = ∏ e, (P e).expect (f e) := by
  unfold FinProb.expect
  change (∑ x : (∀ e, A e), (∏ e, (P e).w (x e)) * ∏ e, f e (x e)) = _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (e : E) (z : A e) => (P e).w z * f e z)).symm

section Graph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    {A : E → Type*} [∀ e, Fintype (A e)]

def Across (ends : E → V × V) (u v : V) (e : E) : Prop :=
  (u = (ends e).1 ∧ v = (ends e).2) ∨ (u = (ends e).2 ∧ v = (ends e).1)

def Step (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (x : ∀ e, A e) (a b : V × ℕ) : Prop :=
  a.1 ∈ s ∧ b.1 ∈ s ∧ ∃ e, Across ends a.1 b.1 e ∧ hit e (x e) = some b.2 ∧ b.2 ≤ a.2

def Reach (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (x : ∀ e, A e) (roots : List (V × ℕ)) (b : V × ℕ) : Prop :=
  ∃ a ∈ roots, Relation.ReflTransGen (Step ends hit s x) a b

noncomputable def closure (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (x : ∀ e, A e) (roots : List (V × ℕ)) : Finset V :=
  Finset.univ.filter fun v => ∃ c, Reach ends hit s x roots (v, c)

def offspring (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (u : V) (c : ℕ) (e : E) (z : A e) : List (V × ℕ) :=
  match hit e z with
  | none => []
  | some d => if d ≤ c then
      (if (ends e).1 = u ∧ (ends e).2 ∈ s then [((ends e).2, d)] else []) ++
      (if (ends e).2 = u ∧ (ends e).1 ∈ s then [((ends e).1, d)] else [])
    else []

noncomputable def children (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (u : V) (c : ℕ) (x : ∀ e, A e) : List (V × ℕ) :=
  Finset.univ.toList.flatMap fun e => offspring ends hit s u c e (x e)

def moment (H : V → ℕ → ℝ) (roots : List (V × ℕ)) : ℝ :=
  (roots.map fun a => H a.1 a.2).prod

theorem offspring_mem (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (u v : V) (c d : ℕ) (e : E) (z : A e) :
    (v, d) ∈ offspring ends hit s u c e z ↔
      v ∈ s ∧ Across ends u v e ∧ hit e z = some d ∧ d ≤ c := by
  classical
  cases h : hit e z with
  | none => simp [offspring, h]
  | some k =>
    by_cases hk : k ≤ c
    · simp only [offspring, h, if_pos hk, List.mem_append]
      by_cases h1 : (ends e).1 = u ∧ (ends e).2 ∈ s <;>
        by_cases h2 : (ends e).2 = u ∧ (ends e).1 ∈ s <;>
          simp [h1, h2, Across, Prod.mk.injEq] <;> aesop
    · simp [offspring, h, hk]
      intro hv hacross hkd
      subst d
      omega

theorem children_mem (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (u v : V) (c d : ℕ) (x : ∀ e, A e) :
    (v, d) ∈ children ends hit s u c x ↔
      v ∈ s ∧ ∃ e, Across ends u v e ∧ hit e (x e) = some d ∧ d ≤ c := by
  simp only [children, List.mem_flatMap, Finset.mem_toList, Finset.mem_univ, true_and,
    offspring_mem]
  aesop

theorem path_bounds (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (x : ∀ e, A e) {a b : V × ℕ} (ha : a.1 ∈ s)
    (h : Relation.ReflTransGen (Step ends hit s x) a b) : b.1 ∈ s ∧ b.2 ≤ a.2 := by
  induction h with
  | refl => exact ⟨ha, le_rfl⟩
  | tail h hstep ih =>
    exact ⟨hstep.2.1, le_trans hstep.2.2.choose_spec.2.2 ih.2⟩

theorem closure_delete (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (x : ∀ e, A e) (roots : List (V × ℕ)) (u : V) (c : ℕ)
    (hroots : ∀ a ∈ roots, a.1 ∈ s ∧ a.2 ≤ c) :
    closure ends hit s x roots ⊆ insert u
      (closure ends hit (s.erase u) x
        (roots.filter (fun a => a.1 ≠ u) ++ children ends hit (s.erase u) u c x)) := by
  classical
  intro v hv
  rcases (Finset.mem_filter.mp hv).2 with ⟨d, a, haroot, hp⟩
  let newroots := roots.filter (fun a => a.1 ≠ u) ++ children ends hit (s.erase u) u c x
  have transfer : ∀ {b : V × ℕ}, Relation.ReflTransGen (Step ends hit s x) a b →
      b.1 = u ∨ Reach ends hit (s.erase u) x newroots b := by
    intro b hpath
    induction hpath with
    | refl =>
      by_cases hau : a.1 = u
      · exact Or.inl hau
      · exact Or.inr ⟨a, List.mem_append_left _ (List.mem_filter.mpr ⟨haroot, by simpa using hau⟩),
          Relation.ReflTransGen.refl⟩
    | @tail b z hpath hstep ih =>
      by_cases hzu : z.1 = u
      · exact Or.inl hzu
      · right
        have hzS : z.1 ∈ s.erase u := Finset.mem_erase.mpr ⟨hzu, hstep.2.1⟩
        rcases hstep.2.2 with ⟨e, he, hhit, hdb⟩
        rcases ih with hbu | ⟨r, hr, hrpath⟩
        · have hbc : b.2 ≤ c := le_trans (path_bounds ends hit s x (hroots a haroot).1 hpath).2
            (hroots a haroot).2
          have hzroot : z ∈ children ends hit (s.erase u) u c x := by
            rw [← (Prod.mk.eta : (z.1, z.2) = z), children_mem]
            exact ⟨hzS, e, by simpa [hbu] using he, hhit, le_trans hdb hbc⟩
          exact ⟨z, List.mem_append_right _ hzroot, Relation.ReflTransGen.refl⟩
        · have hbu : b.1 ≠ u := by
            have hrS : r.1 ∈ s.erase u := by
              rcases List.mem_append.mp hr with hr | hr
              · rcases List.mem_filter.mp hr with ⟨hr, hne⟩
                exact Finset.mem_erase.mpr ⟨by simpa using hne, (hroots r hr).1⟩
              · rcases (children_mem ends hit (s.erase u) u r.1 c r.2 x).mp
                  (by simpa using hr) with ⟨h, _⟩
                exact h
            exact (Finset.mem_erase.mp (path_bounds ends hit (s.erase u) x hrS hrpath).1).1
          exact ⟨r, hr, Relation.ReflTransGen.tail hrpath
            ⟨Finset.mem_erase.mpr ⟨hbu, hstep.1⟩, hzS, e, he, hhit, hdb⟩⟩
  rcases transfer hp with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, h⟩))

def star (ends : E → V × V) (u : V) : Finset E :=
  Finset.univ.filter fun e => u = (ends e).1 ∨ u = (ends e).2

theorem step_mix (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (u : V) (x y : ∀ e, A e) :
    Step ends hit (s.erase u) (mix (star ends u) x y) = Step ends hit (s.erase u) y := by
  funext a b
  apply propext
  have hn : ∀ e, a.1 ∈ s.erase u → b.1 ∈ s.erase u → Across ends a.1 b.1 e →
      e ∉ star ends u := by
    intro e ha hb he hs
    have hneA := (Finset.mem_erase.mp ha).1
    have hneB := (Finset.mem_erase.mp hb).1
    have hs := (Finset.mem_filter.mp hs).2
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hs with hs | hs <;> aesop
  constructor <;> rintro ⟨ha, hb, e, he, hh, hd⟩
  · exact ⟨ha, hb, e, he, by simpa [mix, hn e ha hb he] using hh, hd⟩
  · exact ⟨ha, hb, e, he, by simpa [mix, hn e ha hb he] using hh, hd⟩

theorem children_mix (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (s : Finset V) (u : V) (c : ℕ) (x y : ∀ e, A e) :
    children ends hit s u c (mix (star ends u) x y) = children ends hit s u c x := by
  unfold children
  congr 1
  funext e
  by_cases he : e ∈ star ends u
  · simp [mix, he]
  · have he' : (ends e).1 ≠ u ∧ (ends e).2 ≠ u := by
      simpa [star, eq_comm] using he
    cases h : hit e (x e) <;> cases h' : hit e (mix (star ends u) x y e) <;>
      simp [offspring, h, h', he']

theorem moment_append (H : V → ℕ → ℝ) (a b : List (V × ℕ)) :
    moment H (a ++ b) = moment H a * moment H b := by
  simp [moment]

theorem moment_ge_one (H : V → ℕ → ℝ) (hH : ∀ u c, 1 ≤ H u c)
    (roots : List (V × ℕ)) : 1 ≤ moment H roots := by
  induction roots with
  | nil => simp [moment]
  | cons a roots ih =>
    simpa [moment] using one_le_mul_of_one_le_of_one_le (hH a.1 a.2) ih

theorem moment_children (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (H : V → ℕ → ℝ) (s : Finset V) (u : V) (c : ℕ) (x : ∀ e, A e) :
    moment H (children ends hit s u c x) =
      ∏ e, moment H (offspring ends hit s u c e (x e)) := by
  have hm (l : List E) :
      moment H (l.flatMap fun e => offspring ends hit s u c e (x e)) =
      (l.map fun e => moment H (offspring ends hit s u c e (x e))).prod := by
    induction l with
    | nil => simp [moment]
    | cons e l ih => rw [List.flatMap_cons, moment_append, ih]; simp
  unfold children
  rw [hm, Finset.prod_map_toList]

theorem moment_filter_le (H : V → ℕ → ℝ) (hH : ∀ u c, 1 ≤ H u c)
    (p : V × ℕ → Bool) (roots : List (V × ℕ)) :
    moment H (roots.filter p) ≤ moment H roots := by
  induction roots with
  | nil => simp [moment]
  | cons a roots ih =>
    have hn : 0 ≤ moment H roots := le_trans (by norm_num) (moment_ge_one H hH roots)
    by_cases hp : p a = true
    · simpa [moment, List.filter_cons, hp] using
        mul_le_mul_of_nonneg_left ih (le_trans (by norm_num) (hH a.1 a.2))
    · have hh : moment H roots ≤ H a.1 a.2 * moment H roots := by
        nlinarith [hH a.1 a.2]
      simpa [moment, List.filter_cons, hp] using le_trans ih hh

theorem moment_remove (H : V → ℕ → ℝ) (hH : ∀ u c, 1 ≤ H u c)
    (roots : List (V × ℕ)) {u : V} {c : ℕ} (hmem : (u, c) ∈ roots) :
    H u c * moment H (roots.filter (fun a => a.1 ≠ u)) ≤ moment H roots := by
  induction roots with
  | nil => simp at hmem
  | cons a roots ih =>
    by_cases hau : a.1 = u
    · simp only [List.filter_cons, hau, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        if_false]
      rcases List.mem_cons.mp hmem with ha | hmem
      · cases ha
        have hf : moment H (roots.filter (fun a => a.1 ≠ u)) ≤ moment H roots := by
          exact moment_filter_le H hH _ roots
        simpa [moment] using mul_le_mul_of_nonneg_left hf (le_trans (by norm_num) (hH u c))
      · have hh := ih hmem
        have hrest := moment_ge_one H hH roots
        have hnon : 0 ≤ moment H roots := le_trans (by norm_num) hrest
        have hmul : moment H roots ≤ H a.1 a.2 * moment H roots := by
          nlinarith [hH a.1 a.2]
        exact le_trans hh (by simpa [moment] using hmul)
    · simp only [List.filter_cons, hau, ne_eq, not_false_eq_true, decide_true,
        if_true]
      have hmem' : (u, c) ∈ roots := by
        rcases List.mem_cons.mp hmem with h | h
        · cases h
          exact False.elim (hau rfl)
        · exact h
      have hh := mul_le_mul_of_nonneg_left (ih hmem') (le_trans (by norm_num) (hH a.1 a.2))
      simpa [moment, mul_left_comm] using hh

/-- Delete a highest-cutoff root, integrate its independent incident coordinates, and continue on the
remaining endpoints. Repeated endpoint requests may be retained as separate roots: their product only
increases the bound. -/
theorem domination (ends : E → V × V) (hit : ∀ e, A e → Option ℕ)
    (P : ∀ e, FinProb (A e)) (H : V → ℕ → ℝ) (T : ℕ) (δ' : ℝ)
    (hδ' : 0 ≤ δ') (hH : ∀ u c, 1 ≤ H u c)
    (hlocal : ∀ (s : Finset V) u c, c ≤ T →
      Real.exp δ' * (∏ e, (P e).expect (fun z => moment H (offspring ends hit s u c e z))) ≤ H u c)
    (s : Finset V) (roots : List (V × ℕ))
    (hroots : ∀ a ∈ roots, a.1 ∈ s ∧ a.2 ≤ T) :
    (FinProb.pi P).expect (fun x => Real.exp (δ' * (closure ends hit s x roots).card)) ≤
      moment H roots := by
  classical
  induction s using Finset.strongInductionOn generalizing roots with
  | _ s ih =>
    by_cases hnil : roots = []
    · subst roots
      have hz (x : ∀ e, A e) : closure ends hit s x [] = ∅ := by
        ext v
        simp [closure, Reach]
      simp_rw [hz]
      simp [FinProb.expect_const, moment]
    · have hn : roots.toFinset.Nonempty := by
        exact (List.toFinset_nonempty_iff roots).mpr hnil
      obtain ⟨r, hr, hmax⟩ := roots.toFinset.exists_max_image Prod.snd hn
      have hr' : r ∈ roots := List.mem_toFinset.mp hr
      let u := r.1
      let c := r.2
      have hu : u ∈ s := (hroots r hr').1
      have hc : c ≤ T := (hroots r hr').2
      let old := roots.filter (fun a => a.1 ≠ u)
      let newroots (x : ∀ e, A e) := old ++ children ends hit (s.erase u) u c x
      have hnew (x) : ∀ a ∈ newroots x, a.1 ∈ s.erase u ∧ a.2 ≤ T := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_filter.mp ha with ⟨ha, hne⟩
          exact ⟨Finset.mem_erase.mpr ⟨by simpa using hne, (hroots a ha).1⟩, (hroots a ha).2⟩
        · rcases (children_mem ends hit (s.erase u) u a.1 c a.2 x).mp
            (by simpa using ha) with ⟨ha, e, _, _, hd⟩
          exact ⟨ha, le_trans hd hc⟩
      have hinner (x) : (FinProb.pi P).expect (fun y =>
          Real.exp (δ' * (closure ends hit s (mix (star ends u) x y) roots).card)) ≤
          Real.exp δ' * moment H (newroots x) := by
        have hcl (y) : closure ends hit s (mix (star ends u) x y) roots ⊆
            insert u (closure ends hit (s.erase u) y (newroots x)) := by
          have hh := closure_delete ends hit s (mix (star ends u) x y) roots u c
            (fun a ha => ⟨(hroots a ha).1, hmax a (List.mem_toFinset.mpr ha)⟩)
          rw [children_mix] at hh
          change closure ends hit s (mix (star ends u) x y) roots ⊆ insert u
            (closure ends hit (s.erase u) (mix (star ends u) x y) (newroots x)) at hh
          have heq : closure ends hit (s.erase u) (mix (star ends u) x y) (newroots x) =
              closure ends hit (s.erase u) y (newroots x) := by
            ext v
            simp only [closure, Finset.mem_filter, Finset.mem_univ, true_and]
            simp only [Reach]
            rw [step_mix]
          rw [heq] at hh
          exact hh
        calc
          (FinProb.pi P).expect (fun y =>
              Real.exp (δ' * (closure ends hit s (mix (star ends u) x y) roots).card)) ≤
              (FinProb.pi P).expect (fun y => Real.exp δ' *
                Real.exp (δ' * (closure ends hit (s.erase u) y (newroots x)).card)) := by
            apply FinProb.expect_mono
            intro y
            rw [← Real.exp_add]
            apply Real.exp_le_exp.mpr
            have hcard := le_trans (Finset.card_le_card (hcl y))
              (Finset.card_insert_le u (closure ends hit (s.erase u) y (newroots x)))
            have hcast : ((closure ends hit s (mix (star ends u) x y) roots).card : ℝ) ≤
                (closure ends hit (s.erase u) y (newroots x)).card + 1 := by exact_mod_cast hcard
            nlinarith
          _ = Real.exp δ' * (FinProb.pi P).expect (fun y =>
                Real.exp (δ' * (closure ends hit (s.erase u) y (newroots x)).card)) :=
            FinProb.expect_smul _ _ _
          _ ≤ Real.exp δ' * moment H (newroots x) :=
            mul_le_mul_of_nonneg_left
              (ih (s.erase u) (Finset.erase_ssubset hu) (newroots x) (hnew x)) (Real.exp_pos _).le
      calc
        (FinProb.pi P).expect (fun x => Real.exp (δ' * (closure ends hit s x roots).card)) =
            (FinProb.pi P).expect (fun x => (FinProb.pi P).expect (fun y =>
              Real.exp (δ' * (closure ends hit s (mix (star ends u) x y) roots).card))) :=
          expect_resample P (star ends u) _
        _ ≤ (FinProb.pi P).expect (fun x => Real.exp δ' * moment H (newroots x)) :=
          FinProb.expect_mono _ hinner
        _ = moment H old * (Real.exp δ' *
              ∏ e, (P e).expect (fun z => moment H (offspring ends hit (s.erase u) u c e z))) := by
          simp_rw [newroots, moment_append, moment_children]
          have he : (fun (x : ∀ e, A e) => Real.exp δ' * (moment H old *
              ∏ e, moment H (offspring ends hit (s.erase u) u c e (x e)))) =
              fun (x : ∀ e, A e) => (moment H old * Real.exp δ') *
                ∏ e, moment H (offspring ends hit (s.erase u) u c e (x e)) := by
            funext x
            ring
          rw [he, FinProb.expect_smul,
            expect_prod P (fun e z => moment H (offspring ends hit (s.erase u) u c e z))]
          ring
        _ ≤ moment H old * H u c := mul_le_mul_of_nonneg_left
          (hlocal (s.erase u) u c hc) (le_trans (by norm_num) (moment_ge_one H hH old))
        _ ≤ moment H roots := by
          rw [mul_comm]
          exact moment_remove H hH roots (by simpa [u, c] using hr')

end Graph

section Clock

open HypercubeRamsey.Clock

variable {T : ℕ} {R : Type*} [Fintype R] [DecidableEq R] {g : ℕ}
    {Ω : R → Type*} [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]

def clockEnds (e : RowLabel R g) : Endpoint R g × Endpoint R g := (.inl e.1, .inr e.2)

def clockHit (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (e : RowLabel R g) (z : MeshClockValue T (Ω e.1)) : Option ℕ :=
  match (ins e).getD z with
  | .noArrival => none
  | .tick t _ => some (t.val + 1)

def Hends (Hrow Hlab : ℕ → ℝ) (u : Endpoint R g) (c : ℕ) : ℝ :=
  match u with
  | .inl _ => Hrow c
  | .inr _ => Hlab c

def tickExcess {A : Type*} (H : ℕ → ℝ) (c : ℕ) (z : MeshClockValue T A) : ℝ :=
  match z with
  | .noArrival => 0
  | .tick t _ => if t.val < c then H (t.val + 1) - 1 else 0

theorem tickExcess_nonneg {A : Type*} (H : ℕ → ℝ) (hH : ∀ c, 1 ≤ H c)
    (c : ℕ) (z : MeshClockValue T A) : 0 ≤ tickExcess H c z := by
  cases z with
  | noArrival => exact le_rfl
  | tick t o => simp only [tickExcess]; split_ifs <;> linarith [hH (t.val + 1)]

theorem offspring_bound (Hrow Hlab : ℕ → ℝ)
    (hr : ∀ c, 1 ≤ Hrow c) (hl : ∀ c, 1 ≤ Hlab c)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (hblock : ∀ e x, ins e = some x → x = MeshClockValue.noArrival)
    (s : Finset (Endpoint R g)) (u : Endpoint R g) (c : ℕ) (e : RowLabel R g)
    (z : MeshClockValue T (Ω e.1)) :
    moment (Hends Hrow Hlab) (offspring clockEnds (clockHit ins) s u c e z) ≤
      1 + if EdgeIncident u e then tickExcess (Hends Hrow Hlab (edgeOther u e)) c z else 0 := by
  rcases e with ⟨a, y⟩
  cases hins : ins (a, y) with
  | some w =>
    have hw := hblock (a, y) w hins
    subst w
    simp only [offspring, clockHit, hins, Option.getD_some, moment, List.map_nil, List.prod_nil]
    split_ifs
    · cases u <;> apply le_add_of_nonneg_right <;> apply tickExcess_nonneg <;> assumption
    · simp
  | none =>
    cases u with
    | inl b =>
      cases z with
      | noArrival => simp [offspring, clockHit, hins, moment, tickExcess, EdgeIncident]
      | tick t o =>
        simp only [offspring, clockHit, hins, Option.getD_none, clockEnds, Hends, edgeOther,
          EdgeIncident, Sum.inl.injEq, Sum.inl_ne_inr, or_false, tickExcess]
        by_cases hab : a = b <;> by_cases ht : t.val < c <;>
          by_cases hs : Sum.inr y ∈ s <;>
            simp [moment, Hends, hab, ht, hs, Nat.succ_le_iff, eq_comm] <;> linarith [hl (t.val + 1)]
    | inr b =>
      cases z with
      | noArrival => simp [offspring, clockHit, hins, moment, tickExcess, EdgeIncident]
      | tick t o =>
        simp only [offspring, clockHit, hins, Option.getD_none, clockEnds, Hends, edgeOther,
          EdgeIncident, Sum.inr.injEq, Sum.inr_ne_inl, false_or, tickExcess]
        by_cases hyb : y = b <;> by_cases ht : t.val < c <;>
          by_cases hs : Sum.inl a ∈ s <;>
            simp [moment, Hends, hyb, ht, hs, Nat.succ_le_iff, eq_comm] <;> linarith [hr (t.val + 1)]

theorem original_closure_subset (ξ : ClockField T R g Ω)
    (ins : ∀ e : RowLabel R g, Option (MeshClockValue T (Ω e.1)))
    (roots : Finset (Endpoint R g)) :
    closureFrom (insertArrivals ins ξ) roots ⊆
      closure clockEnds (clockHit ins) Finset.univ ξ (roots.toList.map fun u => (u, T)) := by
  classical
  let M := Fintype.card R * g
  let cutoff : ℕ → ℕ := fun h => min T ((h + M - 1) / M)
  have hMpos (e : ClockCandidate T R g Ω) : 0 < M := by
    dsimp [M]
    exact Nat.mul_pos (Fintype.card_pos_iff.mpr ⟨e.1⟩) (lt_of_le_of_lt (Nat.zero_le _) e.2.1.isLt)
  have key_bounds (e : ClockCandidate T R g Ω) :
      e.2.2.1.val * M ≤ eventPriority e ∧ eventPriority e < (e.2.2.1.val + 1) * M := by
    have ha := (Fintype.equivFin R e.1).isLt
    have hy := e.2.1.isLt
    have hoff : (Fintype.equivFin R e.1).val * g + e.2.1.val < Fintype.card R * g := by
      calc
        _ < (Fintype.equivFin R e.1).val * g + g := Nat.add_lt_add_left hy _
        _ = ((Fintype.equivFin R e.1).val + 1) * g := by ring
        _ ≤ Fintype.card R * g := Nat.mul_le_mul_right g (Nat.succ_le_of_lt ha)
    dsimp [eventPriority, M]
    constructor
    · omega
    · nlinarith only [hoff]
  have tick_le {e : ClockCandidate T R g Ω} {h : ℕ} (he : eventPriority e < h) :
      e.2.2.1.val + 1 ≤ cutoff h := by
    have hMp := hMpos e
    have hk := (key_bounds e).1
    dsimp [cutoff]
    apply le_min (Nat.succ_le_of_lt e.2.2.1.isLt)
    apply (Nat.le_div_iff_mul_le hMp).mpr
    have hpos : 0 < h := lt_of_le_of_lt (Nat.zero_le _) he
    have hsum : (e.2.2.1.val + 1) * M ≤ h + M - 1 := by
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    exact hsum
  have child_le (e : ClockCandidate T R g Ω) : cutoff (eventPriority e) ≤ e.2.2.1.val + 1 := by
    have hMp := hMpos e
    have hk := (key_bounds e).2
    dsimp [cutoff]
    apply le_trans (min_le_right _ _)
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hMp).mpr
    have hsum : eventPriority e + M - 1 < (e.2.2.1.val + 2) * M := by
      simp only [Nat.add_mul, Nat.two_mul] at hk ⊢
      omega
    simpa [Nat.add_assoc] using hsum
  have root_cutoff (r : Endpoint R g) (hr : r ∈ roots) : cutoff (rootHorizon T R g) ≤ T := min_le_left _ _
  intro v hv
  rcases (Finset.mem_filter.mp hv).2 with ⟨h, r, hr, hp⟩
  have transfer : ∀ {b : BackwardPoint T R g},
      Relation.ReflTransGen (backwardStep (insertArrivals ins ξ)) (r, rootHorizon T R g) b →
      ∃ d, cutoff b.2 ≤ d ∧
        Reach clockEnds (clockHit ins) Finset.univ ξ (roots.toList.map fun u => (u, T)) (b.1, d) := by
    intro b hp
    induction hp with
    | refl =>
      exact ⟨T, root_cutoff r hr, (r, T), List.mem_map.mpr ⟨r, Finset.mem_toList.mpr hr, rfl⟩,
        Relation.ReflTransGen.refl⟩
    | @tail b z hp hstep ih =>
      rcases ih with ⟨d, hd, a, ha, hpath⟩
      rcases hstep with ⟨e, he, hk, hz, hends⟩
      have hh : clockHit ins (e.1, e.2.1) (ξ (e.1, e.2.1)) = some (e.2.2.1.val + 1) := by
        simp only [candidateIsArrival, insertArrivals] at he
        simp [clockHit, he]
      refine ⟨e.2.2.1.val + 1, ?_, a, ha, Relation.ReflTransGen.tail hpath ?_⟩
      · simpa [hz] using child_le e
      · refine ⟨Finset.mem_univ _, Finset.mem_univ _, (e.1, e.2.1), ?_, hh, le_trans (tick_le hk) hd⟩
        simpa [Across, clockEnds] using hends
  rcases transfer hp with ⟨d, _, hreach⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hreach⟩

end Clock

end

end HypercubeRamsey.Lane_sol_clock_branch
