import HypercubeRamsey.S16.Comparisons
import HypercubeRamsey.S15.Defs

namespace HypercubeRamsey.S16.Lane_q_s16_prod2

open Classical
open Filter
open HypercubeRamsey
open scoped BigOperators

/-- A coordinate marginal of the finite product law. -/
theorem finLaw_pi_coordinate_mass {I : Type*} [Fintype I] [DecidableEq I]
    {B : Type*} [Fintype B] [DecidableEq B]
    (law : I → FinLaw B) (i : I) (b : B) :
    (FinLaw.pi law).pr (fun f : I → B => f i = b) = (law i).w b := by
  classical
  simp only [FinLaw.pr, FinLaw.pi]
  calc
    (∑ f : I → B, if f i = b then ∏ j, (law j).w (f j) else 0) =
        ∑ f : I → B, ∏ j, (if j = i then (if f j = b then (law j).w (f j) else 0)
          else (law j).w (f j)) := by
      refine Finset.sum_congr rfl ?_
      intro f hf
      by_cases h : f i = b
      · rw [if_pos h]
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          simp [h]
        · simp [hji]
      · rw [if_neg h]
        have hz : (if i = i then (if f i = b then (law i).w (f i) else 0)
            else (law i).w (f i)) = 0 := by simp [h]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hz]
    _ = ∏ j, ∑ y : B, (if j = i then (if y = b then (law j).w y else 0)
          else (law j).w y) := by
      exact (Fintype.prod_sum (fun (j : I) (y : B) => if j = i then
        (if y = b then (law j).w y else 0) else (law j).w y)).symm
    _ = (law i).w b := by
      have hfactor : ∀ j, (∑ y : B, (if j = i then (if y = b then (law j).w y else 0)
            else (law j).w y)) = if j = i then (law i).w b else 1 := by
        intro j
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji, FinLaw.sum_one]
      calc
        (∏ j, ∑ y : B, (if j = i then (if y = b then (law j).w y else 0)
            else (law j).w y)) = ∏ j, (if j = i then (law i).w b else 1) := by
          apply Finset.prod_congr rfl
          intro j hj
          exact hfactor j
        _ = (law i).w b := by simp

/-- Pushforward preserves expectation, with the function composed with its map. -/
theorem finLaw_map_E {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (g : β → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  classical
  unfold FinLaw.E FinLaw.map
  calc
    (∑ b, (∑ a, if f a = b then P.w a else 0) * g b) =
        ∑ b, ∑ a, (if f a = b then P.w a else 0) * g b := by
      congr 1
      funext b
      rw [Finset.sum_mul]
    _ = ∑ a, ∑ b, (if f a = b then P.w a else 0) * g b := by
      rw [Finset.sum_comm]
    _ = ∑ a, P.w a * g (f a) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ b, (if f a = b then P.w a else 0) * g b) =
            (if f a = f a then P.w a * g (f a) else 0) := by
          simp
        _ = P.w a * g (f a) := by simp

/-- Equal observables on the support of a finite law have equal expectations. -/
theorem finLaw_E_congr_of_supported {α : Type*} [Fintype α]
    (P : FinLaw α) (f g : α → ℝ)
    (h : ∀ a, P.w a ≠ 0 → f a = g a) : P.E f = P.E g := by
  unfold FinLaw.E
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hzero : P.w a = 0
  · simp [hzero]
  · simp [h a hzero]

/-- Expectation under a conditional finite law is the restricted weighted sum
divided by the mass of the conditioning event. -/
theorem finLaw_cond_E {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (s : Finset α) (hs : 0 < ∑ x ∈ s, P.w x) (f : α → ℝ) :
    (FinLaw.cond P s hs).E f = (∑ x ∈ s, P.w x * f x) / (∑ x ∈ s, P.w x) := by
  letI : DecidableEq α := Classical.decEq α
  dsimp [FinLaw.E, FinLaw.cond]
  calc
    (∑ x, (if x ∈ s then P.w x else 0) / (∑ y ∈ s, P.w y) * f x) =
        (∑ x, if x ∈ s then P.w x * f x else 0) / (∑ y ∈ s, P.w y) := by
      calc
        (∑ x, (if x ∈ s then P.w x else 0) / (∑ y ∈ s, P.w y) * f x) =
            ∑ x, (if x ∈ s then P.w x * f x else 0) / (∑ y ∈ s, P.w y) := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxs : x ∈ s <;> simp [hxs, div_mul_eq_mul_div]
        _ = (∑ x, if x ∈ s then P.w x * f x else 0) / (∑ y ∈ s, P.w y) := by
          rw [← Finset.sum_div]
    _ = (∑ x ∈ s, P.w x * f x) / (∑ y ∈ s, P.w y) := by
      congr 1
      rw [← Finset.sum_filter]
      simp

/-- A restricted weighted sum is an expectation of the event-masked function. -/
theorem finLaw_E_finset {α : Type*} [Fintype α] [DecidableEq α]
    (P : FinLaw α) (s : Finset α) (f : α → ℝ) :
    P.E (fun x => if x ∈ s then f x else 0) = ∑ x ∈ s, P.w x * f x := by
  classical
  unfold FinLaw.E
  calc
    (∑ x, P.w x * (if x ∈ s then f x else 0)) =
        ∑ x, if x ∈ s then P.w x * f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxs : x ∈ s <;> simp [hxs]
    _ = ∑ x ∈ s, P.w x * f x := by
      rw [← Finset.sum_filter]
      simp

/-- Probabilities of a mapped finite law are pullbacks of the event. -/
theorem finLaw_map_pr {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (A : β → Prop) :
    (FinLaw.map P f).pr A = P.pr (fun a => A (f a)) := by
  classical
  simp only [FinLaw.pr, FinLaw.map]
  calc
    (∑ ω, if A ω then ∑ a, if f a = ω then P.w a else 0 else 0) =
        ∑ ω, ∑ a, if A ω ∧ f a = ω then P.w a else 0 := by
      refine Finset.sum_congr rfl ?_
      intro ω hω
      by_cases hA : A ω <;> simp [hA]
    _ = ∑ a, ∑ ω, if A ω ∧ f a = ω then P.w a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a, if A (f a) then P.w a else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      by_cases hA : A (f a)
      · calc
          (∑ ω, if A ω ∧ f a = ω then P.w a else 0) =
              ∑ ω, if f a = ω then P.w a else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            by_cases heq : f a = ω
            · subst ω
              simp [hA]
            · simp [heq]
          _ = if A (f a) then P.w a else 0 := by simp [hA]
      · calc
          (∑ ω, if A ω ∧ f a = ω then P.w a else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro ω hω
            by_cases heq : f a = ω
            · subst ω
              simp [hA]
            · simp [heq]
          _ = if A (f a) then P.w a else 0 := by simp [hA]

/-- The mass of an atom in an event is bounded by the event probability. -/
theorem finLaw_weight_le_pr {α : Type*} [Fintype α] (P : FinLaw α)
    (A : α → Prop) (ω : α) (hA : A ω) : P.w ω ≤ P.pr A := by
  classical
  unfold FinLaw.pr
  have hsum := Finset.single_le_sum
    (f := fun x => if A x then P.w x else 0)
    (fun x hx => by
      by_cases h : A x
      · simpa [h] using P.nonneg x
      · simp [h])
    (Finset.mem_univ ω)
  simpa [hA] using hsum

/-- Probabilities under a sequential finite-law draw are conditional sums. -/
theorem finLaw_bind_pr {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α × β → Prop) :
    (FinLaw.bind P K).pr A =
      ∑ a, P.w a * (K a).pr (fun b => A (a, b)) := by
  classical
  simp only [FinLaw.pr, FinLaw.bind]
  calc
    (∑ p : α × β, if A p then P.w p.1 * (K p.1).w p.2 else 0) =
        ∑ a, ∑ b, if A (a, b) then P.w a * (K a).w b else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a, P.w a * ∑ b, if A (a, b) then (K a).w b else 0 := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hA : A (a, b) <;> simp [hA]
    _ = ∑ a, P.w a * (K a).pr (fun b => A (a, b)) := rfl

/-- The first marginal of a sequential finite-law draw is its initial law. -/
theorem finLaw_bind_pr_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (K : α → FinLaw β) (A : α → Prop) :
    (FinLaw.bind P K).pr (fun p => A p.1) = P.pr A := by
  classical
  rw [finLaw_bind_pr]
  have hconst : ∀ a, (K a).pr (fun _ => A a) = if A a then 1 else 0 := by
    intro a
    by_cases hA : A a <;> simp [FinLaw.pr, hA, (K a).sum_one]
  simp_rw [hconst]
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hA : A a <;> simp [hA]

/-- The second marginal of a draw with a constant continuation law. -/
theorem finLaw_bind_pr_snd {α β : Type*} [Fintype α] [Fintype β]
    (P : FinLaw α) (Q : FinLaw β) (A : β → Prop) :
    (FinLaw.bind P (fun _ => Q)).pr (fun p => A p.2) = Q.pr A := by
  classical
  rw [finLaw_bind_pr]
  change (∑ a : α, P.w a * Q.pr A) = Q.pr A
  rw [← Finset.sum_mul, P.sum_one]
  ring

/-- A map followed by a deterministic finite-law draw has the expected pushforward event mass. -/
theorem finLaw_map_bind_dirac_pr {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (P : FinLaw Ω) (f : Ω → α) (g : α → β) (E : α × β → Prop) :
    (FinLaw.bind (FinLaw.map P f) (fun a => FinLaw.dirac (g a))).pr E =
      P.pr (fun ω => E (f ω, g (f ω))) := by
  rw [finLaw_bind_pr]
  have hdir : ∀ a, (FinLaw.dirac (g a)).pr (fun b => E (a, b)) =
      if E (a, g a) then 1 else 0 := by
    intro a
    change (∑ b : β, if E (a, b) then if b = g a then (1 : ℝ) else 0 else 0) =
      (if E (a, g a) then (1 : ℝ) else 0)
    calc
      (∑ b, if E (a, b) then if b = g a then (1 : ℝ) else 0 else 0) =
          ∑ b, if b = g a then (if E (a, b) then (1 : ℝ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases heq : b = g a <;> simp [heq]
      _ = if E (a, g a) then (1 : ℝ) else 0 := by simp [Finset.sum_ite_eq']
  simp_rw [hdir]
  calc
    (∑ a, (FinLaw.map P f).w a * (if E (a, g a) then 1 else 0)) =
        (FinLaw.map P f).pr (fun a => E (a, g a)) := by
      unfold FinLaw.pr
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hE : E (a, g a) <;> simp [hE]
    _ = P.pr (fun ω => E (f ω, g (f ω))) :=
      finLaw_map_pr P f (fun a => E (a, g a))

/-- A positive atom in a mapped law has a positive preimage atom. -/
theorem finLaw_map_nonzero_preimage {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (P : FinLaw α) (f : α → β) (b : β)
    (hb : (FinLaw.map P f).w b ≠ 0) : ∃ a, f a = b ∧ P.w a ≠ 0 := by
  classical
  by_contra h
  have hsum : (∑ a, if f a = b then P.w a else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hEq : f a = b
    · have hzero : P.w a = 0 := by
        by_contra hn
        exact h ⟨a, hEq, hn⟩
      simp [hEq, hzero]
    · simp [hEq]
  exact hb (by simpa [FinLaw.map] using hsum)

/-- Finite-law extensionality from equality of weights. -/
theorem finLaw_ext {α : Type*} [Fintype α] {P Q : FinLaw α}
    (h : ∀ a, P.w a = Q.w a) : P = Q := by
  cases P with
  | mk wP hP0 hP1 =>
    cases Q with
    | mk wQ hQ0 hQ1 =>
      have hw : wP = wQ := funext h
      subst wQ
      have hnonneg : hP0 = hQ0 := Subsingleton.elim _ _
      have hsum : hP1 = hQ1 := Subsingleton.elim _ _
      subst hnonneg
      subst hsum
      rfl

/-- Mapping a finite law through the identity preserves the law. -/
theorem finLaw_map_id {α : Type*} [Fintype α] [DecidableEq α] (P : FinLaw α) :
    FinLaw.map P id = P := by
  apply finLaw_ext
  intro a
  simp [FinLaw.map]

/-- The probability of a singleton event equals its atom weight. -/
theorem finLaw_pr_singleton {α : Type*} [Fintype α] (P : FinLaw α) (a : α) :
    P.pr (fun x => x = a) = P.w a := by
  classical
  unfold FinLaw.pr
  simp [Finset.sum_ite_eq']

/-- Expectations of a function of one coordinate under a finite product law. -/
theorem finLaw_pi_E_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (law : ∀ i, FinLaw (Ω i)) (i : I) (f : Ω i → ℝ) :
    (FinLaw.pi law).E (fun ω => f (ω i)) = (law i).E f := by
  classical
  unfold FinLaw.E FinLaw.pi
  calc
    (∑ ω : (∀ j : I, Ω j), (∏ j : I, (law j).w (ω j)) * f (ω i)) =
        ∑ ω : (∀ j : I, Ω j), ∏ j : I, (law j).w (ω j) *
          (if hji : j = i then f (hji ▸ ω j) else 1) := by
      apply Finset.sum_congr rfl
      intro ω hω
      have hdelta :
          (∏ j, if hji : j = i then f (hji ▸ ω j) else (1 : ℝ)) = f (ω i) := by
        simp
      calc
        (∏ j, (law j).w (ω j)) * f (ω i) =
            (∏ j, (law j).w (ω j)) *
              (∏ j, if hji : j = i then f (hji ▸ ω j) else (1 : ℝ)) := by rw [hdelta]
        _ = ∏ j, (law j).w (ω j) *
              (if hji : j = i then f (hji ▸ ω j) else 1) := by
          rw [← Finset.prod_mul_distrib]
    _ = ∏ j, ∑ x : Ω j, (law j).w x *
          (if hji : j = i then f (hji ▸ x) else 1) := by
      exact (Fintype.prod_sum fun (j : I) (x : Ω j) =>
        (law j).w x * (if hji : j = i then f (hji ▸ x) else 1)).symm
    _ = (law i).E f := by
      have hfactor : ∀ j,
          (∑ x : Ω j, (law j).w x *
            (if hji : j = i then f (hji ▸ x) else 1)) =
            if j = i then (law i).E f else 1 := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [FinLaw.E]
        · simp [hji, FinLaw.sum_one]
      simp only [hfactor]
      simp

/-- A cylinder event through one assignment coordinate is determined by that row law. -/
theorem finLaw_pr_map_coordinate {I O B : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype B] [DecidableEq B]
    (Q : FinLaw (I → O)) (p : I → FinLaw O)
    (hmarg : ∀ i o, Q.pr (fun x => x i = o) = (p i).w o)
    (i : I) (f : O → B) (A : B → Prop) :
    Q.pr (fun x => A (f (x i))) = (FinLaw.map (p i) f).pr A := by
  classical
  have hcoord : FinLaw.map Q (fun x => x i) = p i := by
    apply finLaw_ext
    intro y
    calc
      (FinLaw.map Q (fun x => x i)).w y =
          (FinLaw.map Q (fun x => x i)).pr (fun z => z = y) :=
            (finLaw_pr_singleton _ y).symm
      _ = Q.pr (fun x => x i = y) := finLaw_map_pr Q (fun x => x i) (fun z => z = y)
      _ = (p i).w y := hmarg i y
  calc
    Q.pr (fun x => A (f (x i))) =
        (FinLaw.map Q (fun x => x i)).pr (fun y => A (f y)) :=
          (finLaw_map_pr Q (fun x => x i) (fun y => A (f y))).symm
    _ = (p i).pr (fun y => A (f y)) := by rw [hcoord]
    _ = (FinLaw.map (p i) f).pr A :=
          (finLaw_map_pr (p i) f A).symm

/-- Replacing an event on all positive atoms preserves its finite probability. -/
theorem finLaw_pr_congr_of_supported {α : Type*} [Fintype α] (P : FinLaw α)
    (A B : α → Prop) (h : ∀ a, P.w a ≠ 0 → (A a ↔ B a)) :
    P.pr A = P.pr B := by
  classical
  unfold FinLaw.pr
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hzero : P.w a = 0
  · simp [hzero]
  · simp [h a hzero]

/-- A constant event has probability zero or one according to its truth. -/
theorem finLaw_pr_const {α : Type*} [Fintype α] (P : FinLaw α) (p : Prop) :
    P.pr (fun _ => p) = if p then 1 else 0 := by
  classical
  by_cases hp : p <;> simp [FinLaw.pr, hp, P.sum_one]

/-- Positive event probability has a supported atom in the event. -/
theorem finLaw_pr_pos_has_nonzero_atom {α : Type*} [Fintype α]
    (P : FinLaw α) (A : α → Prop) (hA : 0 < P.pr A) :
    ∃ a, A a ∧ P.w a ≠ 0 := by
  classical
  by_contra hnone
  have hzero : ∀ a, (if A a then P.w a else 0) = 0 := by
    intro a
    by_cases ha : A a
    · have hw : P.w a = 0 := by
        by_contra hne
        exact hnone ⟨a, ha, hne⟩
      simp [ha, hw]
    · simp [ha]
  have hprob : P.pr A = 0 := by
    unfold FinLaw.pr
    apply Finset.sum_eq_zero
    intro a ha
    exact hzero a
  linarith

/-- Probabilities of complementary finite events sum to one. -/
theorem finLaw_pr_compl {α : Type*} [Fintype α] (P : FinLaw α) (A : α → Prop) :
    P.pr A + P.pr (fun a => ¬ A a) = 1 := by
  classical
  letI : DecidablePred A := fun a => Classical.propDecidable (A a)
  letI : DecidablePred (fun a => ¬ A a) := fun a => Classical.propDecidable (¬ A a)
  unfold FinLaw.pr
  calc
    (∑ a, if A a then P.w a else 0) + (∑ a, if ¬ A a then P.w a else 0) =
        ∑ a, P.w a := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hA : A a <;> simp [hA]
    _ = 1 := P.sum_one

/-- The probability of membership in a finite set is its total atom mass. -/
theorem finLaw_pr_finset {α : Type*} [Fintype α] (P : FinLaw α) (s : Finset α) :
    P.pr (fun x => x ∈ s) = ∑ x ∈ s, P.w x := by
  classical
  letI : DecidablePred (fun x : α => x ∈ s) := fun x => Classical.propDecidable (x ∈ s)
  unfold FinLaw.pr
  rw [← Finset.sum_filter]
  simp

/-- Split a finite product at one distinguished coordinate. The other side
stores a unit at that coordinate and the original value at every other one. -/
noncomputable def finLaw_pi_splitEquiv {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] (i₀ : I) :
    (∀ i, Ω i) ≃ (Ω i₀ × (∀ i : {j : I // j ≠ i₀}, Ω i.1)) where
  toFun ω := (ω i₀, fun i => ω i.1)
  invFun p i := if h : i = i₀ then h.symm ▸ p.1 else p.2 ⟨i, h⟩
  left_inv ω := by
    funext i
    by_cases h : i = i₀
    · subst i
      simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨x, a⟩
    apply Prod.ext
    · simp
    · funext i
      by_cases h : i.1 = i₀
      · exact (i.2 h).elim
      · change (if h' : i.1 = i₀ then h'.symm ▸ x else a ⟨i.1, h'⟩) = a i
        simp [h]

/-- The product law factors through `finLaw_pi_splitEquiv` into its
distinguished coordinate and the independent product on the remaining ones. -/
theorem finLaw_pi_split {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (law : ∀ i, FinLaw (Ω i)) (i₀ : I)
    [Fintype {j : I // j ≠ i₀}] :
    FinLaw.map (FinLaw.pi law) (finLaw_pi_splitEquiv i₀) =
      FinLaw.bind (law i₀) (fun _ => FinLaw.pi (fun i : {j : I // j ≠ i₀} => law i.1)) := by
  classical
  apply finLaw_ext
  intro p
  rcases p with ⟨x, a⟩
  let e := finLaw_pi_splitEquiv (Ω := Ω) i₀
  change (∑ ω, if e ω = (x, a) then ∏ i, (law i).w (ω i) else 0) = _
  rw [Finset.sum_eq_single (e.symm (x, a))]
  · simp only [e, Equiv.apply_symm_apply, if_true]
    have hprod :
        (∏ i, (law i).w ((finLaw_pi_splitEquiv (Ω := Ω) i₀).symm (x, a) i)) =
          (law i₀).w x * ∏ i : {j : I // j ≠ i₀}, (law i.1).w (a i) := by
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (s := Finset.univ) (i := i₀) (by simp)]
      congr 1
      · simp [finLaw_pi_splitEquiv]
      · rw [Finset.prod_subtype (p := fun j : I => j ≠ i₀)
          (s := Finset.univ \ {i₀}) (h := by intro j; simp)]
        apply Finset.prod_congr rfl
        intro j hj
        have hj' : j.1 ≠ i₀ := j.2
        simp [finLaw_pi_splitEquiv, hj']
    rw [hprod]
    rfl
  · intro ω hω hne
    have hnot : e ω ≠ (x, a) := by
      intro heq
      apply hne
      apply e.injective
      exact heq.trans (e.apply_symm_apply (x, a)).symm
    simp [hnot]
  · simp

/-- A finite product's coordinate marginal assigns a finite set its factor
mass. -/
theorem finLaw_pi_coordinate_pr {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (law : ∀ i, FinLaw (Ω i)) (i₀ : I) (A : Finset (Ω i₀)) :
    (FinLaw.pi law).pr (fun ω => ω i₀ ∈ A) =
      (law i₀).pr (fun x => x ∈ A) := by
  classical
  let e := finLaw_pi_splitEquiv (Ω := Ω) i₀
  calc
    (FinLaw.pi law).pr (fun ω => ω i₀ ∈ A) =
        (FinLaw.map (FinLaw.pi law) e).pr (fun p => p.1 ∈ A) := by
          symm
          exact finLaw_map_pr _ e (fun p => p.1 ∈ A)
    _ = (FinLaw.bind (law i₀) (fun _ =>
          FinLaw.pi (fun j : {i : I // i ≠ i₀} => law j.1))).pr
          (fun p => p.1 ∈ A) := by rw [finLaw_pi_split]
    _ = (law i₀).pr (fun x => x ∈ A) := by
      rw [finLaw_bind_pr]
      have haux := (FinLaw.pi (fun j : {i : I // i ≠ i₀} => law j.1)).sum_one
      simp [FinLaw.pr, haux]
      have hfin := finLaw_pr_finset (law i₀) A
      unfold FinLaw.pr at hfin
      exact hfin.symm

/-- The cylinder mass of a dependent product law is the product of its
coordinate masses. -/
theorem finLaw_pi_pr_cylinder {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (law : ∀ i, FinLaw (Ω i)) (S : Finset I) (a : ∀ i, Ω i) :
    (FinLaw.pi law).pr (fun ω => ∀ i ∈ S, ω i = a i) =
      ∏ i ∈ S, (law i).w (a i) := by
  letI : DecidablePred (fun ω : (∀ i, Ω i) => ∀ i ∈ S, ω i = a i) :=
    fun ω => Classical.propDecidable _
  unfold FinLaw.pr FinLaw.pi
  calc
    (∑ ω : (∀ i, Ω i), if (∀ i ∈ S, ω i = a i) then
        ∏ i, (law i).w (ω i) else 0) =
      ∑ ω : (∀ i, Ω i), ∏ i, if i ∈ S then
        (if ω i = a i then (law i).w (ω i) else 0) else (law i).w (ω i) := by
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hgood : ∀ i ∈ S, ω i = a i
      · rw [if_pos hgood]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hiS : i ∈ S
        · simp [hiS, hgood i hiS]
        · simp [hiS]
      · push_neg at hgood
        obtain ⟨i, hiS, hneq⟩ := hgood
        have hnot : ¬ ∀ i ∈ S, ω i = a i := by
          intro hall
          exact hneq (hall i hiS)
        have hzero :
            (∏ i, if i ∈ S then
              (if ω i = a i then (law i).w (ω i) else 0) else (law i).w (ω i)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hiS, hneq])
        simp [hnot, hzero]
    _ = ∏ i, ∑ x : Ω i, if i ∈ S then
          (if x = a i then (law i).w x else 0) else (law i).w x :=
        (Fintype.prod_sum (fun (i : I) (x : Ω i) => if i ∈ S then
          (if x = a i then (law i).w x else 0) else (law i).w x)).symm
    _ = ∏ i, if i ∈ S then (law i).w (a i) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiS : i ∈ S
      · simp [hiS, Finset.sum_eq_single (a i)]
      · simp [hiS, FinLaw.sum_one]
    _ = ∏ i ∈ S, (law i).w (a i) := by
      rw [← Finset.prod_filter]
      simp

/-- Projecting a product law onto a finite coordinate subtype gives the
product law of precisely those factors. -/
theorem finLaw_pi_project {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (law : ∀ i, FinLaw (Ω i)) (S : Finset I)
    [Fintype {i : I // i ∈ S}] :
    FinLaw.map (FinLaw.pi law) (fun ω => fun i : {j : I // j ∈ S} => ω i.1) =
      FinLaw.pi (fun i : {j : I // j ∈ S} => law i.1) := by
  classical
  let default : ∀ i, Ω i := fun i => by
    have htrue : 0 < (law i).pr (fun _ => True) := by
      rw [finLaw_pr_const]
      norm_num
    exact Classical.choose
      (finLaw_pr_pos_has_nonzero_atom (law i) (fun _ => True) htrue)
  apply finLaw_ext
  intro a
  let extA : ∀ i, Ω i := fun i => if hi : i ∈ S then a ⟨i, hi⟩ else default i
  have hproject (ω : ∀ i, Ω i) :
      ((fun i : {j : I // j ∈ S} => ω i.1) = a) ↔
        ∀ i ∈ S, ω i = extA i := by
    constructor
    · intro heq i hi
      have h := congrFun heq ⟨i, hi⟩
      simpa [extA, hi] using h
    · intro heq
      funext i
      have h := heq i.1 i.2
      simpa [extA, i.2] using h
  have hmass :
      (∑ ω : (∀ i : I, Ω i),
        if (fun i : {j : I // j ∈ S} => ω i.1) = a then
          ∏ i : I, (law i).w (ω i) else 0) =
        ∏ i : {j : I // j ∈ S}, (law i.1).w (a i) := by
    calc
      _ = (FinLaw.pi law).pr (fun ω => ∀ i ∈ S, ω i = extA i) := by
        unfold FinLaw.pr FinLaw.pi
        apply Finset.sum_congr rfl
        intro ω hω
        simp [hproject]
      _ = ∏ i ∈ S, (law i).w (extA i) := finLaw_pi_pr_cylinder law S extA
      _ = ∏ i : {j : I // j ∈ S}, (law i.1).w (a i) := by
        rw [Finset.prod_subtype (p := fun i : I => i ∈ S) (s := S)
          (h := by intro i; simp)]
        apply Finset.prod_congr rfl
        intro i hi
        simp [extA, hi]
  change (∑ ω : (∀ i : I, Ω i),
      if (fun i : {j : I // j ∈ S} => ω i.1) = a then
        ∏ i, (law i).w (ω i) else 0) =
    ∏ i : {j : I // j ∈ S}, (law i.1).w (a i)
  exact hmass

/-- Conditioning the first coordinate of a product leaves its independent
second coordinate unchanged. -/
theorem finLaw_cond_bind_left {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (P : FinLaw α) (Q : FinLaw β) (s : Finset α)
    (h : 0 < ∑ a ∈ s, P.w a) :
    FinLaw.cond (FinLaw.bind P (fun _ => Q))
        (Finset.univ.filter fun z : α × β => z.1 ∈ s)
        (by
          have hp : (FinLaw.bind P (fun _ => Q)).pr
              (fun z => z.1 ∈ s) = ∑ a ∈ s, P.w a := by
            classical
            rw [finLaw_bind_pr]
            unfold FinLaw.pr
            calc
              (∑ a, P.w a * Q.pr (fun _ => a ∈ s)) =
                  ∑ a, if a ∈ s then P.w a else 0 := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [finLaw_pr_const]
                by_cases hmem : a ∈ s <;> simp [hmem]
              _ = ∑ a ∈ s, P.w a := by
                rw [← Finset.sum_filter]
                simp
          have hset : (FinLaw.bind P (fun _ => Q)).pr
              (fun z => z ∈ Finset.univ.filter (fun z : α × β => z.1 ∈ s)) =
                ∑ a ∈ s, P.w a := by
            simpa using hp
          rw [← Lane_q_s16_prod2.finLaw_pr_finset]
          rw [hset]
          exact h) =
      FinLaw.bind (FinLaw.cond P s h) (fun _ => Q) := by
  classical
  have hmass :
      (FinLaw.bind P (fun _ => Q)).pr
          (fun z => z.1 ∈ s) = ∑ a ∈ s, P.w a := by
    rw [finLaw_bind_pr]
    unfold FinLaw.pr
    calc
      (∑ a, P.w a * Q.pr (fun _ => a ∈ s)) =
          ∑ a, if a ∈ s then P.w a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [finLaw_pr_const]
        by_cases hmem : a ∈ s <;> simp [hmem]
      _ = ∑ a ∈ s, P.w a := by
        rw [← Finset.sum_filter]
        simp
  have hdenom :
      (∑ z ∈ Finset.univ.filter (fun z : α × β => z.1 ∈ s),
        (FinLaw.bind P (fun _ => Q)).w z) = ∑ a ∈ s, P.w a := by
    calc
      (∑ z ∈ Finset.univ.filter (fun z : α × β => z.1 ∈ s),
          (FinLaw.bind P (fun _ => Q)).w z) =
          (FinLaw.bind P (fun _ => Q)).pr
            (fun z => z ∈ Finset.univ.filter (fun z : α × β => z.1 ∈ s)) :=
        (finLaw_pr_finset _ _).symm
      _ = ∑ a ∈ s, P.w a := by
        simpa [Finset.mem_filter] using hmass
  apply finLaw_ext
  intro z
  rcases z with ⟨a, b⟩
  have hwt : (FinLaw.bind P (fun _ => Q)).w (a, b) = P.w a * Q.w b := by
    simp [FinLaw.bind]
  simp only [FinLaw.cond]
  rw [hdenom]
  by_cases ha : a ∈ s <;> simp [FinLaw.bind, hwt, ha] <;> ring

/-- An eventual index property becomes a dimension cutoff along any sequence
whose finitely many early dimensions are bounded. -/
theorem badSeq_dimension_cutoff (S : BadSeq) {P : ℕ → Prop}
    (hP : ∀ᶠ k in Filter.atTop, P k) :
    ∃ n₀ : ℕ, ∀ k, n₀ ≤ S.n k → P k := by
  classical
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hP
  refine ⟨(∑ k ∈ Finset.range k₀, S.n k) + 1, ?_⟩
  intro k hk
  by_contra hnot
  have hklt : k < k₀ := by
    by_contra hnotlt
    exact hnot (hk₀ k (Nat.le_of_not_gt hnotlt))
  have hsum : S.n k ≤ ∑ j ∈ Finset.range k₀, S.n j :=
    Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_range.mpr hklt)
  omega

/-- Convert a polynomially scaled tail into an eighth of the inverse cube. -/
theorem exp_poly_to_neg3_eighth {n : ℕ} (hn : 0 < n) (e : ℝ)
    (he : (n : ℝ) ^ 3 * e ≤ 1 / 8) :
    e ≤ (n : ℝ) ^ (-3 : ℝ) / 8 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcube : 0 < (n : ℝ) ^ 3 := by positivity
  have hdiv : e ≤ (1 / 8 : ℝ) / (n : ℝ) ^ 3 :=
    (le_div_iff₀ hcube).2 (by nlinarith [he])
  have hpow : (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ 3)⁻¹ := by
    calc
      (n : ℝ) ^ (-3 : ℝ) = ((n : ℝ) ^ (3 : ℝ))⁻¹ :=
        Real.rpow_neg (le_of_lt hnR) 3
      _ = ((n : ℝ) ^ 3)⁻¹ :=
        congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (n : ℝ) 3)
  calc
    e ≤ (1 / 8 : ℝ) / (n : ℝ) ^ 3 := hdiv
    _ = (n : ℝ) ^ (-3 : ℝ) / 8 := by
      rw [hpow]
      field_simp [ne_of_gt hcube]

/-- The calibration exponentials and the fourth-power error eventually fit
inside one eighth of the cubic slack. -/
theorem exp_denominator_slack_cutoff (c : ℝ) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ))) ≤ (n : ℝ) ^ (-3 : ℝ) / 8 ∧
      Real.exp (-(c * (n : ℝ)) / 2) ≤ (n : ℝ) ^ (-3 : ℝ) / 8 ∧
      (n : ℝ) ^ (-4 : ℝ) ≤ (n : ℝ) ^ (-3 : ℝ) / 8 := by
  have hrootAtTop : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hgatePoly : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 6 *
        Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ)))) atTop (nhds 0) := by
    simpa [Function.comp_def, one_mul, neg_one_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 1 one_pos).comp hrootAtTop
  have hpowEq (n : ℕ) : ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 6 = (n : ℝ) ^ 3 := by
    calc
      ((n : ℝ) ^ (1 / 2 : ℝ)) ^ 6 =
          ((n : ℝ) ^ (1 / 2 : ℝ)) ^ (6 : ℝ) :=
        (Real.rpow_natCast ((n : ℝ) ^ (1 / 2 : ℝ)) 6).symm
      _ = (n : ℝ) ^ ((1 / 2 : ℝ) * 6) := by
        rw [← Real.rpow_mul (Nat.cast_nonneg n)]
      _ = (n : ℝ) ^ (3 : ℝ) := by
        rw [show (1 / 2 : ℝ) * 6 = 3 by norm_num]
      _ = (n : ℝ) ^ 3 := Real.rpow_natCast _ _
  have hgatePolyNat : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ))))
      atTop (nhds 0) := by
    apply Tendsto.congr' (Filter.Eventually.of_forall ?_) hgatePoly
    intro n
    rw [hpowEq n]
  have hpermPoly : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * Real.exp (-((c / 2) * (n : ℝ))))
      atTop (nhds 0) := by
    simpa [Function.comp_def, one_mul, neg_one_mul, mul_assoc] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 (c / 2)
        (by positivity : 0 < c / 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨nGate, hnGate⟩ := Filter.eventually_atTop.mp
    (hgatePolyNat.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  obtain ⟨nPerm, hnPerm⟩ := Filter.eventually_atTop.mp
    (hpermPoly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)))
  refine ⟨max nGate (max nPerm 8), ?_⟩
  intro n hn
  have hnGate' : nGate ≤ n := (le_max_left _ _).trans hn
  have hnPerm' : nPerm ≤ n :=
    (le_trans (le_max_left nPerm 8) (le_max_right nGate (max nPerm 8))).trans hn
  have hn8 : 8 ≤ n :=
    (le_trans (le_max_right nPerm 8) (le_max_right nGate (max nPerm 8))).trans hn
  have hnpos : 0 < n := by omega
  have hgateMul : (n : ℝ) ^ 3 *
      Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ))) < 1 / 8 := hnGate n hnGate'
  have hgate : Real.exp (-((n : ℝ) ^ (1 / 2 : ℝ))) ≤
      (n : ℝ) ^ (-3 : ℝ) / 8 :=
    exp_poly_to_neg3_eighth hnpos _ (le_of_lt hgateMul)
  have hpermMul : (n : ℝ) ^ 3 *
      Real.exp (-((c / 2) * (n : ℝ))) < 1 / 8 := hnPerm n hnPerm'
  have hpermArg : -(c * (n : ℝ)) / 2 = -((c / 2) * (n : ℝ)) := by ring
  have hperm : Real.exp (-(c * (n : ℝ)) / 2) ≤
      (n : ℝ) ^ (-3 : ℝ) / 8 := by
    rw [hpermArg]
    exact exp_poly_to_neg3_eighth hnpos _ (le_of_lt hpermMul)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn8R : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn8
  have hpow : (n : ℝ) ^ (-4 : ℝ) = (n : ℝ) ^ (-3 : ℝ) / (n : ℝ) := by
    rw [show (-4 : ℝ) = (-3 : ℝ) - 1 by norm_num, Real.rpow_sub hnR, Real.rpow_one]
  have hqNonneg : 0 ≤ (n : ℝ) ^ (-3 : ℝ) := Real.rpow_nonneg (le_of_lt hnR) _
  have hfourth : (n : ℝ) ^ (-4 : ℝ) ≤ (n : ℝ) ^ (-3 : ℝ) / 8 := by
    rw [hpow]
    exact div_le_div_of_nonneg_left hqNonneg (by norm_num) hn8R
  exact ⟨hgate, hperm, hfourth⟩

/-- Three denominator losses of size at most one eighth of a common slack
combine within that slack. -/
theorem inverse_three_slacks {x y z q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hx : x ≤ q / 8) (hy : y ≤ q / 8) (hz : z ≤ q / 8) :
    (1 - x)⁻¹ * (1 - y)⁻¹ * (1 - z)⁻¹ ≤ 1 + q := by
  have hx1 : x ≤ 1 := by nlinarith [hx, hq1]
  have hy1 : y ≤ 1 := by nlinarith [hy, hq1]
  have hz1 : z ≤ 1 := by nlinarith [hz, hq1]
  have hxpos : 0 < 1 - x := by linarith
  have hypos : 0 < 1 - y := by linarith
  have hzpos : 0 < 1 - z := by linarith
  have hxy : 0 ≤ x * y := mul_nonneg hx0 hy0
  have hxz : 0 ≤ x * z := mul_nonneg hx0 hz0
  have hyz : 0 ≤ y * z := mul_nonneg hy0 hz0
  have hxyz : x * y * z ≤ x * y := by
    calc
      x * y * z = (x * y) * z := by ring
      _ ≤ (x * y) * 1 := mul_le_mul_of_nonneg_left hz1 hxy
      _ = x * y := by ring
  have hexpand :
      (1 - x) * (1 - y) * (1 - z) =
        1 - x - y - z + (x * y + x * z + y * z - x * y * z) := by ring
  have hprodLower : 1 - x - y - z ≤ (1 - x) * (1 - y) * (1 - z) := by
    rw [hexpand]
    nlinarith [hxy, hxz, hyz, hxyz]
  have hsum : x + y + z ≤ 3 * q / 8 := by linarith
  have hprodBound : 1 - 3 * q / 8 ≤ (1 - x) * (1 - y) * (1 - z) := by
    linarith
  have hprodPos : 0 < (1 - x) * (1 - y) * (1 - z) := by
    have hlow : 0 < 1 - 3 * q / 8 := by nlinarith [hq0, hq1]
    exact lt_of_lt_of_le hlow hprodBound
  have hfinal : 1 ≤ (1 + q) * ((1 - x) * (1 - y) * (1 - z)) := by
    have hbase : 1 ≤ (1 + q) * (1 - 3 * q / 8) := by nlinarith [hq0, hq1]
    calc
      1 ≤ (1 + q) * (1 - 3 * q / 8) := hbase
      _ ≤ (1 + q) * ((1 - x) * (1 - y) * (1 - z)) :=
        mul_le_mul_of_nonneg_left hprodBound (by positivity)
  calc
    (1 - x)⁻¹ * (1 - y)⁻¹ * (1 - z)⁻¹ =
        1 / ((1 - x) * (1 - y) * (1 - z)) := by
      field_simp [ne_of_gt hxpos, ne_of_gt hypos, ne_of_gt hzpos]
    _ ≤ 1 + q := (div_le_iff₀ hprodPos).2 hfinal

/-- The explicit exponential permission-mass loss supplied by the bad-label
average, incidence ratio, and incoming-bin atom cap. -/
theorem permission_mass_explicit_lower {Group Bin Label Incidence : Type*}
    [Fintype Group] [DecidableEq Group] [Fintype Bin] [DecidableEq Bin]
    [Fintype Label] [DecidableEq Label] [Fintype Incidence] [DecidableEq Incidence]
    (P : PermissionTable Group Bin Label Incidence) (qin : Group → FinLaw Bin)
    (hP : PermissionLossHypotheses P qin) (g : Group) :
    1 - Real.exp (-(P.cperm * (P.n : ℝ)) / 2) ≤
      ∑ D ∈ P.permitted g, (qin g).w D := by
  classical
  let x : ℝ := P.cperm * (P.n : ℝ)
  let tau : ℝ := Real.exp (-x)
  let incs : Finset Incidence := permissionIncidences P g
  let badLabels : Incidence → Finset Label := fun inc =>
    Finset.univ.filter fun y => tau < P.badMass inc y
  let badBins : Finset Bin := (P.permitted g)ᶜ
  let cover : Finset Bin := incs.biUnion fun inc =>
    (badLabels inc).biUnion fun y => binsContainingLabel P y
  have hx : 0 < x := mul_pos P.cperm_pos (by exact_mod_cast P.n_pos)
  have htau : 0 < tau := Real.exp_pos _
  have hbadCard : ∀ inc, (badLabels inc).card ≤
      Real.exp (-2 * x) * (Fintype.card Label : ℝ) := by
    intro inc
    have hlarge : ((badLabels inc).card : ℝ) * tau ≤
        ∑ y ∈ badLabels inc, P.badMass inc y := by
      calc
        ((badLabels inc).card : ℝ) * tau = ∑ y ∈ badLabels inc, tau := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ badLabels inc, P.badMass inc y := by
          apply Finset.sum_le_sum
          intro y hy
          exact (Finset.mem_filter.mp hy).2.le
    have hsub : (∑ y ∈ badLabels inc, P.badMass inc y) ≤
        ∑ y, P.badMass inc y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro y hy _
      exact (hP.mean_bad_mass inc y).1
    have havg : (∑ y, P.badMass inc y) ≤
        Real.exp (-3 * x) * (Fintype.card Label : ℝ) := by
      simpa [x, mul_assoc, mul_left_comm, mul_comm] using hP.average_bad_mass inc
    have hbound : ((badLabels inc).card : ℝ) * tau ≤
        Real.exp (-3 * x) * (Fintype.card Label : ℝ) := hlarge.trans (hsub.trans havg)
    have hdiv : (badLabels inc).card ≤
        (Real.exp (-3 * x) * (Fintype.card Label : ℝ)) / tau :=
      (le_div_iff₀ htau).2 hbound
    calc
      (badLabels inc).card ≤
          (Real.exp (-3 * x) * (Fintype.card Label : ℝ)) / tau := hdiv
      _ = Real.exp (-2 * x) * (Fintype.card Label : ℝ) := by
        dsimp [tau]
        calc
          (Real.exp (-3 * x) * (Fintype.card Label : ℝ)) / Real.exp (-x) =
              (Real.exp (-3 * x) / Real.exp (-x)) * (Fintype.card Label : ℝ) := by ring
          _ = Real.exp (-2 * x) * (Fintype.card Label : ℝ) := by
            rw [← Real.exp_sub]
            congr 1
            ring_nf
  have hcoverSubset : badBins ⊆ cover := by
    intro D hD
    have hnotPerm : D ∉ P.permitted g := Finset.mem_compl.mp hD
    have hnotGood : ¬ ∀ inc, P.groupOf inc = g →
        ∀ y, y ∈ P.labels D → P.badMass inc y ≤ tau := by
      intro hgood
      apply hnotPerm
      apply (P.permitted_iff g D).2
      intro inc hinc y hy
      have hy' := hgood inc hinc y hy
      simpa [x, tau, mul_assoc, mul_left_comm, mul_comm] using hy'
    push_neg at hnotGood
    obtain ⟨inc, hinc, y, hy, hbad⟩ := hnotGood
    have hincMem : inc ∈ incs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩
    have hyBad : y ∈ badLabels inc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩
    have hbin : D ∈ binsContainingLabel P y := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    exact Finset.mem_biUnion.mpr ⟨inc, hincMem,
      Finset.mem_biUnion.mpr ⟨y, hyBad, hbin⟩⟩
  have hcoverCard : cover.card ≤ ∑ inc ∈ incs, (badLabels inc).card := by
    calc
      cover.card ≤ ∑ inc ∈ incs, ((badLabels inc).biUnion (fun y => binsContainingLabel P y)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ inc ∈ incs, (badLabels inc).card := by
        apply Finset.sum_le_sum
        intro inc hi
        calc
          ((badLabels inc).biUnion (fun y => binsContainingLabel P y)).card ≤
              ∑ y ∈ badLabels inc, (binsContainingLabel P y).card := Finset.card_biUnion_le
          _ ≤ ∑ y ∈ badLabels inc, 1 := by
            apply Finset.sum_le_sum
            intro y hy
            exact hP.labels_disjoint y
          _ = (badLabels inc).card := by simp
  have hcoverReal : (cover.card : ℝ) ≤
      (incs.card : ℝ) * Real.exp (-2 * x) * (Fintype.card Label : ℝ) := by
    calc
      (cover.card : ℝ) ≤ ∑ inc ∈ incs, ((badLabels inc).card : ℝ) := by exact_mod_cast hcoverCard
      _ ≤ ∑ inc ∈ incs, Real.exp (-2 * x) * (Fintype.card Label : ℝ) := by
        apply Finset.sum_le_sum
        intro inc hi
        exact hbadCard inc
      _ = (incs.card : ℝ) * Real.exp (-2 * x) * (Fintype.card Label : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hincRatio :
      (incs.card : ℝ) * ((Fintype.card Label : ℝ) / Fintype.card Bin) ≤ Real.exp x := by
    simpa [incs, x] using hP.incidence_label_ratio g
  have hbinCardPos : 0 < (Fintype.card Bin : ℝ) := by
    obtain ⟨b⟩ := hP.bins_nonempty
    letI : Nonempty Bin := ⟨b⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Bin)
  have hcap : ∀ D, (qin g).w D ≤ Real.exp (x / 2) / Fintype.card Bin := by
    intro D
    simpa [x] using hP.incoming_cap g D
  have hremoved : (∑ D ∈ badBins, (qin g).w D) ≤ Real.exp (-x / 2) := by
    calc
      (∑ D ∈ badBins, (qin g).w D) ≤ ∑ D ∈ cover, (qin g).w D := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hcoverSubset
        intro D hD hcoverD
        exact (qin g).nonneg D
      _ ≤ ∑ D ∈ cover, Real.exp (x / 2) / Fintype.card Bin := by
        apply Finset.sum_le_sum
        intro D hD
        exact hcap D
      _ = (cover.card : ℝ) * (Real.exp (x / 2) / Fintype.card Bin) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((incs.card : ℝ) * Real.exp (-2 * x) * (Fintype.card Label : ℝ)) *
          (Real.exp (x / 2) / Fintype.card Bin) :=
        mul_le_mul_of_nonneg_right hcoverReal (div_nonneg (Real.exp_nonneg _) (by positivity))
      _ = ((incs.card : ℝ) * ((Fintype.card Label : ℝ) / Fintype.card Bin)) *
          (Real.exp (-2 * x) * Real.exp (x / 2)) := by ring
      _ ≤ Real.exp x * (Real.exp (-2 * x) * Real.exp (x / 2)) :=
        mul_le_mul_of_nonneg_right hincRatio (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
      _ = Real.exp (-x / 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hpermPr : (qin g).pr (fun D => D ∈ P.permitted g) =
      ∑ D ∈ P.permitted g, (qin g).w D := finLaw_pr_finset (qin g) (P.permitted g)
  have hbadPr : (qin g).pr (fun D => D ∉ P.permitted g) =
      ∑ D ∈ badBins, (qin g).w D := by
    calc
      (qin g).pr (fun D => D ∉ P.permitted g) =
          (qin g).pr (fun D => D ∈ badBins) := by
        apply finLaw_pr_congr_of_supported
        intro D _
        simp [badBins]
      _ = ∑ D ∈ badBins, (qin g).w D := finLaw_pr_finset (qin g) badBins
  have hsplit := finLaw_pr_compl (qin g) (fun D => D ∈ P.permitted g)
  have hsum : (∑ D ∈ P.permitted g, (qin g).w D) +
      (∑ D ∈ badBins, (qin g).w D) = 1 := by
    rw [← hpermPr, ← hbadPr]
    exact hsplit
  change 1 - Real.exp (-x / 2) ≤ ∑ D ∈ P.permitted g, (qin g).w D
  linarith [hsum, hremoved]

/-- A Dirac law assigns an event its indicator at the distinguished state. -/
theorem finLaw_dirac_pr {α : Type*} [Fintype α] [DecidableEq α] (x : α) (A : α → Prop) :
    (FinLaw.dirac x).pr A = if A x then 1 else 0 := by
  classical
  change (∑ y, if A y then if y = x then (1 : ℝ) else 0 else 0) =
      (if A x then 1 else 0)
  calc
    (∑ y, if A y then if y = x then (1 : ℝ) else 0 else 0) =
        ∑ y, if y = x then (if A y then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases h : y = x <;> simp [h]
    _ = if A x then 1 else 0 := by simp [Finset.sum_ite_eq']

end HypercubeRamsey.S16.Lane_q_s16_prod2
