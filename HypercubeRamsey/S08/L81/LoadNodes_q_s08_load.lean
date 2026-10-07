import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2
import HypercubeRamsey.S08.L81.PosteriorNodes
import HypercubeRamsey.S07.TagStage

/-!
Private helpers for lane q-s08-load.
-/

noncomputable section

namespace HypercubeRamsey.S08.Lane_q_s08_load

open Classical
open Filter
open OAI.HypercubeRamsey
open scoped BigOperators

private theorem pr_bind_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (B : α × β → Prop) :
    (FinProb.bind P K).pr B = ∑ a, P.w a * (K a).pr (fun b => B (a, b)) := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : B (a, b) <;> simp [h, mul_assoc]

private theorem pr_le_one {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A ≤ 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ a, if A a then P.w a else 0) ≤ ∑ a, P.w a :=
      Finset.sum_le_sum fun a _ => by split_ifs <;> simp [P.nonneg a]
    _ = 1 := P.sum_eq_one

private theorem pr_mono {α : Type*} [Fintype α] (P : FinProb α)
    (A B : α → Prop) (hAB : ∀ ω, A ω → B ω) : P.pr A ≤ P.pr B := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro ω _
  by_cases hA : A ω
  · have hB := hAB ω hA
    simp [hA, hB]
  · by_cases hB : B ω <;> simp [hA, hB, P.nonneg ω]

private theorem pr_compl {α : Type*} [Fintype α] (P : FinProb α) (A : α → Prop) :
    P.pr A + P.pr (fun a => ¬ A a) = 1 := by
  classical
  letI : DecidablePred A := fun a => Classical.propDecidable (A a)
  letI : DecidablePred (fun a => ¬ A a) := fun a => Classical.propDecidable (¬ A a)
  unfold FinProb.pr
  rw [← Finset.sum_add_distrib]
  calc
    (∑ a, ((if A a then P.w a else 0) +
      @ite ℝ ((fun x => ¬ A x) a) (Classical.propDecidable _) (P.w a) 0)) =
        ∑ a, P.w a := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases hA : A a <;> simp [hA]
    _ = 1 := P.sum_eq_one

private theorem pr_positive_weight_eq_one {α : Type*} [Fintype α] (P : FinProb α) :
    P.pr (fun a => 0 < P.w a) = 1 := by
  classical
  unfold FinProb.pr
  calc
    (∑ a, if 0 < P.w a then P.w a else 0) = ∑ a, P.w a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : 0 < P.w a
      · simp [h]
      · have hzero : P.w a = 0 := le_antisymm (le_of_not_gt h) (P.nonneg a)
        simp [h, hzero]
    _ = 1 := P.sum_eq_one

private theorem pr_le_on_support {α : Type*} [Fintype α] (P : FinProb α)
    (S E : α → Prop) (hbad : P.pr (fun a => ¬ S a) = 0) :
    P.pr E ≤ P.pr (fun a => S a ∧ E a) := by
  calc
    P.pr E ≤ P.pr (fun a => (S a ∧ E a) ∨ ¬ S a) := by
      apply pr_mono
      intro a hE
      by_cases hS : S a <;> simp [hS, hE]
    _ ≤ P.pr (fun a => S a ∧ E a) + P.pr (fun a => ¬ S a) :=
      FinProb.pr_union P (fun a => S a ∧ E a) (fun a => ¬ S a)
    _ = P.pr (fun a => S a ∧ E a) := by rw [hbad]; ring

private theorem expect_congr {α : Type*} [Fintype α] (P : FinProb α)
    (f g : α → ℝ) (h : ∀ x, f x = g x) : P.expect f = P.expect g := by
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]

private theorem expect_nonneg {α : Type*} [Fintype α] (P : FinProb α)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ P.expect f := by
  unfold FinProb.expect
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (P.nonneg x) (hf x)

private theorem pr_bind_le {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (B : α × β → Prop) (A : α → Prop) (c : ℝ)
    (hc : 0 ≤ c)
    (h : ∀ a, P.w a ≠ 0 → ¬ A a → (K a).pr (fun b => B (a, b)) ≤ c) :
    (FinProb.bind P K).pr B ≤ P.pr A + c := by
  rw [pr_bind_eq]
  have hpt (a : α) : P.w a * (K a).pr (fun b => B (a, b)) ≤
      (if A a then P.w a else 0) + P.w a * c := by
    have hw := P.nonneg a
    by_cases hA : A a
    · simp only [hA, if_true]
      have hle := mul_le_mul_of_nonneg_left (pr_le_one (K a) fun b => B (a, b)) hw
      have htail : 0 ≤ P.w a * c := mul_nonneg hw hc
      nlinarith
    · simp only [hA, if_false, zero_add]
      by_cases hw0 : P.w a = 0
      · simp [hw0]
      · exact mul_le_mul_of_nonneg_left (h a hw0 hA) hw
  calc
    (∑ a, P.w a * (K a).pr (fun b => B (a, b))) ≤
        ∑ a, ((if A a then P.w a else 0) + P.w a * c) :=
      Finset.sum_le_sum fun a _ => hpt a
    _ = P.pr A + c := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_eq_one]
      simp [FinProb.pr]

private theorem pi_expect_prodCoords {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : ∀ i, Ω i → ℝ) :
    (FinProb.pi P).expect (fun ω => ∏ i ∈ s, f i (ω i)) =
      ∏ i ∈ s, (P i).expect (f i) := by
  classical
  let g : (∀ i : {i // i ∈ s}, Ω i.1) → ℝ := fun a => ∏ i, f i.1 (a i)
  have hprod (ω : ∀ i, Ω i) :
      (∏ i ∈ s, f i (ω i)) = g (fun i => ω i.1) := by
    dsimp [g]
    simpa using (Finset.prod_attach s (fun i => f i (ω i))).symm
  calc
    (FinProb.pi P).expect (fun ω => ∏ i ∈ s, f i (ω i)) =
        (FinProb.pi P).expect (fun ω => g (fun i => ω i.1)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro ω _
      change (FinProb.pi P).w ω * (∏ i ∈ s, f i (ω i)) =
        (FinProb.pi P).w ω * g (fun i => ω i.1)
      rw [hprod ω]
    _ = (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect g :=
      FinProb.pi_marginal_expect P s g
    _ = ∏ i ∈ s, (P i).expect (f i) := by
      simp only [FinProb.expect, FinProb.pi]
      have hpoint (ω : ∀ i : {i // i ∈ s}, Ω i.1) :
          (∏ i : {i // i ∈ s}, (P i.1).w (ω i) * f i.1 (ω i)) =
            (∏ i : {i // i ∈ s}, (P i.1).w (ω i)) *
              ∏ i : {i // i ∈ s}, f i.1 (ω i) := by
        rw [Finset.prod_mul_distrib]
      calc
        (∑ ω : (∀ i : {i // i ∈ s}, Ω i.1),
            (∏ i : {i // i ∈ s}, (P i.1).w (ω i)) *
              ∏ i : {i // i ∈ s}, f i.1 (ω i)) =
            ∑ ω : (∀ i : {i // i ∈ s}, Ω i.1),
              ∏ i : {i // i ∈ s}, (P i.1).w (ω i) * f i.1 (ω i) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact (hpoint ω).symm
        _ = ∏ i : {i // i ∈ s}, ∑ x, (P i.1).w x * f i.1 x := by
          let q : ∀ i : {i // i ∈ s}, Ω i.1 → ℝ :=
            fun i x => (P i.1).w x * f i.1 x
          change (∑ ω : (∀ i : {i // i ∈ s}, Ω i.1), ∏ i, q i (ω i)) =
            ∏ i, ∑ x, q i x
          exact (Fintype.prod_sum q).symm
        _ = ∏ i ∈ s, (P i).expect (f i) := by
          simp only [FinProb.expect]
          rw [Finset.univ_eq_attach]
          exact Finset.prod_attach s (fun i => (P i).expect (f i))

private theorem indicator_forall_prod {ι : Type*} [DecidableEq ι] {Ω : ι → Type*}
    (s : Finset ι) (A : ∀ i, Ω i → Prop) [∀ i, DecidablePred (A i)] (ω : ∀ i, Ω i) :
    (if ∀ i ∈ s, A i (ω i) then (1 : ℝ) else 0) =
      ∏ i ∈ s, if A i (ω i) then (1 : ℝ) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      by_cases ha : A i (ω i)
      · simp [Finset.forall_mem_insert, hi, ih, ha]
      · simp [Finset.forall_mem_insert, hi, ih, ha]

private theorem pi_pr_forall {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (A : ∀ i, Ω i → Prop) [∀ i, DecidablePred (A i)] :
    (FinProb.pi P).pr (fun ω => ∀ i ∈ s, A i (ω i)) =
      ∏ i ∈ s, (P i).pr (A i) := by
  classical
  rw [FinProb.pr_indicator]
  calc
    (FinProb.pi P).expect (fun ω => if ∀ i ∈ s, A i (ω i) then (1 : ℝ) else 0) =
        (FinProb.pi P).expect (fun ω => ∏ i ∈ s, if A i (ω i) then (1 : ℝ) else 0) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro ω _
      change (FinProb.pi P).w ω *
          (if ∀ i ∈ s, A i (ω i) then (1 : ℝ) else 0) =
        (FinProb.pi P).w ω *
          ∏ i ∈ s, if A i (ω i) then (1 : ℝ) else 0
      by_cases hall : ∀ i ∈ s, A i (ω i)
      · have hprod : (∏ i ∈ s, if A i (ω i) then (1 : ℝ) else 0) = 1 := by
          calc
            (∏ i ∈ s, if A i (ω i) then (1 : ℝ) else 0) = ∏ i ∈ s, (1 : ℝ) := by
              apply Finset.prod_congr rfl
              intro i hi
              simp [hall i hi]
            _ = 1 := by simp
        rw [if_pos hall, hprod]
      · have hex : ∃ i ∈ s, ¬ A i (ω i) := by
          by_contra hn
          apply hall
          intro i hi
          by_contra hAi
          exact hn ⟨i, hi, hAi⟩
        obtain ⟨i, hi, hAi⟩ := hex
        have hprod : (∏ i ∈ s, if A i (ω i) then (1 : ℝ) else 0) = 0 :=
          Finset.prod_eq_zero hi (by simp [hAi])
        rw [if_neg hall, hprod]
    _ = ∏ i ∈ s, (P i).expect (fun y => if A i y then (1 : ℝ) else 0) :=
      pi_expect_prodCoords P s (fun i y => if A i y then (1 : ℝ) else 0)
    _ = ∏ i ∈ s, (P i).pr (A i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (FinProb.pr_indicator (P i) (A i)).symm

private theorem tuple_hits_pr {N h : ℕ} (μ : Law N) (E : Fin N → Fin N → Prop)
    (G : Colour) (x : Fin N) :
    (FinProb.pi (fun _ : Fin h => μ)).pr (fun θ => ∀ j, Hits E G x (θ j)) =
      rowDeg E G x μ ^ h := by
  classical
  have hpi : (FinProb.pi (fun _ : Fin h => μ)).pr
      (fun θ : Fin h → Fin N => ∀ j : Fin h, Hits E G x (θ j)) =
        ∏ j ∈ (Finset.univ : Finset (Fin h)), μ.pr (fun y => Hits E G x y) := by
    simpa using (pi_pr_forall (ι := Fin h) (Ω := fun _ => Fin N)
      (P := fun _ : Fin h => μ) Finset.univ
      (fun _ : Fin h => fun y : Fin N => Hits E G x y))
  have h' : (FinProb.pi (fun _ : Fin h => μ)).pr
      (fun θ => ∀ j, Hits E G x (θ j)) =
        ∏ j ∈ (Finset.univ : Finset (Fin h)), μ.pr (fun y => Hits E G x y) := by
    simpa using hpi
  have hq : μ.pr (fun y => Hits E G x y) = rowDeg E G x μ := by
    unfold FinProb.pr rowDeg
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  rw [h', hq]
  simp

private def singletonPiEquiv {α β : Type*} [DecidableEq α] (a : α) :
    (∀ i : {i // i ∈ ({a} : Finset α)}, β) ≃ β where
  toFun z := z ⟨a, by simp⟩
  invFun b := fun _ => b
  left_inv z := by
    funext i
    have hval : i.1 = a := Finset.mem_singleton.mp i.2
    have hi : i = ⟨a, by simp⟩ := Subtype.ext hval
    rw [hi]
  right_inv b := rfl

private theorem pi_singleton_expect {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] (P : α → FinProb β) (a : α) (f : β → ℝ) :
    (FinProb.pi P).expect (fun ω => f (ω a)) = (P a).expect f := by
  classical
  let s : Finset α := {a}
  letI : Unique {i // i ∈ s} :=
    ⟨⟨a, by simp [s]⟩, fun i => Subtype.ext (Finset.mem_singleton.mp (by simpa [s] using i.2))⟩
  let e : (∀ i : {i // i ∈ s}, β) ≃ β := singletonPiEquiv a
  calc
    (FinProb.pi P).expect (fun ω => f (ω a)) =
        (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).expect
          (fun z => f (z ⟨a, by simp [s]⟩)) := by
      simpa [s] using
        (FinProb.pi_marginal_expect P s (fun z => f (z ⟨a, by simp [s]⟩)))
    _ = (P a).expect f := by
      unfold FinProb.expect FinProb.pi
      apply Fintype.sum_equiv e
      intro z
      have hidx : (default : {i // i ∈ s}) = ⟨a, by simp [s]⟩ := by
        apply Subtype.ext
        simp [s]
      simp [e, s, FinProb.pi, singletonPiEquiv, hidx]

private theorem singletonSubtype_expect {α β : Type*} [DecidableEq α]
    [Fintype β] (P : FinProb β) (a : α)
    (f : (∀ i : {i // i ∈ ({a} : Finset α)}, β) → ℝ) :
    (FinProb.pi (fun _ : {i // i ∈ ({a} : Finset α)} => P)).expect f =
      P.expect (fun b => f ((singletonPiEquiv (β := β) a).symm b)) := by
  classical
  let s : Finset α := {a}
  letI : Unique {i // i ∈ s} :=
    ⟨⟨a, by simp [s]⟩,
      fun i => Subtype.ext (Finset.mem_singleton.mp (by simpa [s] using i.2))⟩
  let e : (∀ i : {i // i ∈ ({a} : Finset α)}, β) ≃ β := singletonPiEquiv (β := β) a
  unfold FinProb.expect FinProb.pi
  apply Fintype.sum_equiv e
  intro b
  have hidx : (default : {i // i ∈ s}) = ⟨a, by simp [s]⟩ := by
    apply Subtype.ext
    simp [s]
  have harg : b default = b ⟨a, by simp [s]⟩ := congrArg b hidx
  change (∏ i : {i // i ∈ s}, P.w (b i)) * f b =
    P.w (e b) * f (e.symm (e b))
  rw [Equiv.symm_apply_apply]
  have hprod : (∏ i : {i // i ∈ s}, P.w (b i)) = P.w (e b) := by
    simp [e, s, singletonPiEquiv, hidx, harg]
  rw [hprod]

private abbrev PosOutside {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (g : D.KeyT) :=
  ∀ k : {k : D.KeyT // k ∉ ({g} : Finset D.KeyT)}, D.Loc → Bool

private noncomputable def reconstructPos {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (g : D.KeyT) (P : D.Loc → Bool) (O : PosOutside D g) : D.Pos :=
  fun k => if hk : k = g then P else O ⟨k, by simp [hk]⟩

private theorem reconstructPos_key {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (g : D.KeyT) (P : D.Loc → Bool) (O : PosOutside D g) :
    reconstructPos D g P O g = P := by
  funext ℓ
  simp [reconstructPos]

private theorem rprime_hits_pr {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (x : Fin D.N) :
    D.R'.pr (fun θ => D.hitsAll x θ) =
      ∑ i, D.M.Λ i * rowDeg D.E D.G x (D.M.ν i) ^ h := by
  classical
  unfold Ctx.R'
  rw [FinProb.map_pr, pr_bind_eq]
  apply Finset.sum_congr rfl
  intro i _
  have ht := tuple_hits_pr (h := h) (D.M.ν i) D.E D.G x
  simpa [Ctx.tagLaw, Ctx.hitsAll] using congrArg (fun z => D.M.Λ i * z) ht

private theorem rprime_weight {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (θ : D.Tup) :
    D.R'.w θ = ∑ i, D.M.Λ i * ∏ j, (D.M.ν i).w (θ j) := by
  classical
  change (∑ z : D.M.ι × D.Tup,
      if z.2 = θ then D.M.Λ z.1 * ∏ j, (D.M.ν z.1).w (z.2 j) else 0) = _
  rw [Fintype.sum_prod_type]
  simp [eq_comm]

private theorem postW_expect {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (i : D.M.ι) : D.R'.expect (fun θ => D.postW θ i) = D.M.Λ i := by
  classical
  have hterm (θ : D.Tup) :
      D.R'.w θ * D.postW θ i = D.M.Λ i * ∏ j, (D.M.ν i).w (θ j) := by
    unfold Ctx.postW
    rw [rprime_weight]
    by_cases hz : ∑ j, D.M.Λ j * ∏ k, (D.M.ν j).w (θ k) = 0
    · have hnonneg : ∀ j ∈ (Finset.univ : Finset D.M.ι),
          0 ≤ D.M.Λ j * ∏ k, (D.M.ν j).w (θ k) := by
        intro j hj
        exact mul_nonneg (D.M.Λ_nonneg j) (Finset.prod_nonneg fun k _ => (D.M.ν j).nonneg _)
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ i)
      simp [hz, hzero]
    · simp only [if_neg hz]
      field_simp [hz]
  rw [FinProb.expect]
  calc
    (∑ θ : D.Tup, D.R'.w θ * D.postW θ i) =
        ∑ θ : D.Tup, D.M.Λ i * ∏ j : Fin h, (D.M.ν i).w (θ j) := by
      apply Finset.sum_congr rfl
      intro θ _
      exact hterm θ
    _ = D.M.Λ i := by
      rw [← Finset.mul_sum]
      have hsum : ∑ θ : D.Tup, ∏ j : Fin h, (D.M.ν i).w (θ j) = 1 := by
        simpa [FinProb.pi] using (FinProb.pi (fun _ : Fin h => D.M.ν i)).sum_eq_one
      rw [hsum]
      ring

private theorem raw_postW_expect {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (g : D.KeyT) (i : D.M.ι) :
    D.rawHidden.expect (fun Θ => D.postW (Θ g) i) = D.M.Λ i := by
  classical
  simpa [Ctx.rawHidden] using
    (pi_singleton_expect (P := fun _ : D.KeyT => D.R') g (fun θ => D.postW θ i)).trans
      (postW_expect D i)

private theorem cross_hit_pr {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (g : D.KeyT) (x : Fin D.N) :
    D.rawHidden.pr (fun Θ => D.crossHit Θ g x) =
      (D.R'.pr (fun θ => D.hitsAll x θ)) ^ (crossKeys g).card := by
  classical
  have hpi := pi_pr_forall (P := fun _ : D.KeyT => D.R') (crossKeys g)
    (fun _ θ => D.hitsAll x θ)
  calc
    D.rawHidden.pr (fun Θ => D.crossHit Θ g x) =
        ∏ u ∈ crossKeys g, D.R'.pr (fun θ => D.hitsAll x θ) := by
      simpa [Ctx.rawHidden, Ctx.crossHit] using hpi
    _ = (D.R'.pr (fun θ => D.hitsAll x θ)) ^ (crossKeys g).card := by simp

private theorem cross_survival_small (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * (sC η₀ n : ℝ) * (n : ℝ) ^ (-(eta8 η₀ / 2)) ≤ Real.log (11 / 10 : ℝ) := by
  have hτ : 0 < tau8 η₀ := by
    rw [tau8_eq]
    unfold eta8
    positivity
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-tau8 η₀)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop hτ).comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hlog : 0 < Real.log (11 / 10 : ℝ) := Real.log_pos (by norm_num)
  have hquarter : 0 < Real.log (11 / 10 : ℝ) / 4 := by positivity
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds hquarter))
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have htau : 1 ≤ (n : ℝ) ^ tau8 η₀ := Real.one_le_rpow hnR hτ.le
  have hsceil : (sC η₀ n : ℝ) ≤ (n : ℝ) ^ tau8 η₀ + 1 := by
    unfold sC
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ tau8 η₀)).le
  have hexp : -(eta8 η₀ / 2) = -2 * tau8 η₀ := by
    rw [tau8_eq]
    ring
  have hpower :
      (n : ℝ) ^ tau8 η₀ * (n : ℝ) ^ (-2 * tau8 η₀) = (n : ℝ) ^ (-tau8 η₀) := by
    calc
      _ = (n : ℝ) ^ (tau8 η₀ + (-2 * tau8 η₀)) := (Real.rpow_add hnpos _ _).symm
      _ = _ := by congr 1 <;> ring
  calc
    2 * (sC η₀ n : ℝ) * (n : ℝ) ^ (-(eta8 η₀ / 2)) ≤
        2 * ((n : ℝ) ^ tau8 η₀ + 1) * (n : ℝ) ^ (-2 * tau8 η₀) := by
          rw [hexp]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsceil (by norm_num)) (by positivity)
    _ ≤ 4 * (n : ℝ) ^ (-tau8 η₀) := by
      have hbase : (n : ℝ) ^ tau8 η₀ + 1 ≤ 2 * (n : ℝ) ^ tau8 η₀ := by linarith
      calc
        2 * ((n : ℝ) ^ tau8 η₀ + 1) * (n : ℝ) ^ (-2 * tau8 η₀) ≤
            2 * (2 * (n : ℝ) ^ tau8 η₀) * (n : ℝ) ^ (-2 * tau8 η₀) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hbase (by norm_num)) (by positivity)
        _ = 4 * ((n : ℝ) ^ tau8 η₀ * (n : ℝ) ^ (-2 * tau8 η₀)) := by ring
        _ = 4 * (n : ℝ) ^ (-tau8 η₀) := by rw [hpower]
    _ ≤ Real.log (11 / 10 : ℝ) := by
      have hsmall := hn₀ n hn0
      nlinarith

private theorem pi_expect_prod_disjoint {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] {Ω : V → Type*} [∀ v, Fintype (Ω v)]
    (P : ∀ v, FinProb (Ω v)) (s : Finset I)
    (f : I → (∀ v, Ω v) → ℝ) (S : I → Finset V)
    (hdep : ∀ i, FinProb.DependsOn (f i) (S i))
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    (FinProb.pi P).expect (fun ω => ∏ i ∈ s, f i ω) =
      ∏ i ∈ s, (FinProb.pi P).expect (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.expect_const]
  | @insert i s hi ih =>
      let U : Finset V := s.biUnion S
      let F : (∀ v, Ω v) → ℝ := fun ω => ∏ j ∈ s, f j ω
      have hFdep : FinProb.DependsOn F U := by
        intro ω ω' hEq
        dsimp [F]
        apply Finset.prod_congr rfl
        intro j hj
        apply hdep j
        intro v hv
        exact hEq v (Finset.mem_biUnion.mpr ⟨j, hj, hv⟩)
      have hUF : Disjoint U (S i) := by
        apply Finset.disjoint_left.mpr
        intro v hvU hvI
        obtain ⟨j, hj, hv⟩ := Finset.mem_biUnion.mp hvU
        have hji : j ≠ i := by
          intro hEq
          subst j
          exact hi hj
        exact (Finset.disjoint_left.mp (hdis j i hji)) hv hvI
      have hfac := FinProb.pi_expect_mul_of_disjoint P F (f i) U (S i)
        hFdep (hdep i) hUF
      calc
        (FinProb.pi P).expect (fun ω => ∏ j ∈ insert i s, f j ω) =
            (FinProb.pi P).expect (fun ω => F ω * f i ω) := by
          apply expect_congr
          intro ω
          simp [F, hi, Finset.prod_insert]
          ring
        _ = (FinProb.pi P).expect F * (FinProb.pi P).expect (f i) := hfac
        _ = (∏ j ∈ s, (FinProb.pi P).expect (f j)) * (FinProb.pi P).expect (f i) := by
          rw [ih]
        _ = ∏ j ∈ insert i s, (FinProb.pi P).expect (f j) := by
          simp [hi, Finset.prod_insert]
          ring

private theorem pi_free_integral_eq {V : Type*} [Fintype V] [DecidableEq V]
    {Ω : V → Type*} [∀ v, Fintype (Ω v)] [∀ v, DecidableEq (Ω v)]
    (P : ∀ v, FinProb (Ω v)) (U : Finset V) (Φ : (∀ v, Ω v) → ℝ)
    (hdep : FinProb.DependsOn Φ U) (ω : ∀ v, Ω v) :
    (∑ a : (∀ v : U, Ω v), (∏ v : U, (P v.1).w (a v)) * Φ (glue U ω a)) =
      (FinProb.pi P).expect Φ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ U) Ω
  have hext (a : ∀ v : {v // v ∈ U}, Ω v.1) :
      e.symm (a, fun v => ω v.1) = glue U ω a := by
    funext v
    by_cases hv : v ∈ U <;> simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, glue, hv]
  calc
    (∑ a : (∀ v : U, Ω v), (∏ v : U, (P v.1).w (a v)) * Φ (glue U ω a)) =
        (FinProb.pi (fun v : {v // v ∈ U} => P v.1)).expect (fun a => Φ (glue U ω a)) := by
      rfl
    _ = (FinProb.pi P).expect Φ := by
      symm
      convert FinProb.pi_expect_depends P U Φ ω hdep using 1
      apply expect_congr
      intro a
      rw [hext]

private noncomputable def bcompCap (η₀ β K : ℝ) (h n : ℕ) : ℝ :=
  32 * K * (2 : ℝ) ^ (h * (2 * sC η₀ n)) *
    Real.exp (h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2))

private theorem bcompCap_small (η₀ β K : ℝ) (h : ℕ) (hη₀ : 0 < η₀)
    (hβτ : β < tau8 η₀ / 4) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (n : ℝ) * fGrid η₀ n * bcompCap η₀ β K h n ≤ 1 := by
  have hτ : 0 < tau8 η₀ := by rw [tau8_eq]; unfold eta8; positivity
  have hβhalf : β < tau8 η₀ / 2 := by linarith
  have hbaseTend : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 100 : ℝ)) atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      tendsto_natCast_atTop_atTop
  have hbaseEv : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (2 * h + 1) ≤ (n : ℝ) ^ (1 / 100 : ℝ) :=
    Filter.tendsto_atTop.1 hbaseTend ((2 : ℝ) ^ (2 * h + 1))
  let nlog : ℕ := Nat.ceil (Real.exp 100)
  have hlogEv : ∀ᶠ n : ℕ in atTop, 100 ≤ Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop nlog] with n hn
    have hceil : Real.exp 100 ≤ (nlog : ℝ) := Nat.le_ceil _
    have hnreal : (nlog : ℝ) ≤ n := by exact_mod_cast hn
    have hle : Real.exp 100 ≤ (n : ℝ) := hceil.trans hnreal
    have hlog := Real.log_le_log (Real.exp_pos 100) hle
    simpa using hlog
  have hhalfTend : Tendsto (fun n : ℕ => (n : ℝ) ^ (tau8 η₀ / 2)) atTop atTop := by
    exact (tendsto_rpow_atTop (by linarith : (0 : ℝ) < tau8 η₀ / 2)).comp
      tendsto_natCast_atTop_atTop
  have hhalfEv : ∀ᶠ n : ℕ in atTop,
      (h : ℝ) + 1 ≤ (n : ℝ) ^ (tau8 η₀ / 2) :=
    Filter.tendsto_atTop.1 hhalfTend ((h : ℝ) + 1)
  have hτTend : Tendsto (fun n : ℕ => (n : ℝ) ^ tau8 η₀) atTop atTop := by
    exact (tendsto_rpow_atTop hτ).comp tendsto_natCast_atTop_atTop
  have hpolyTend : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ tau8 η₀) ^ (10 / tau8 η₀) *
        Real.exp (-2 * (n : ℝ) ^ tau8 η₀)) atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (10 / tau8 η₀) 2 (by norm_num : (0 : ℝ) < 2)).comp hτTend
    simpa [Function.comp_def] using h
  have hpolyScaled : Tendsto
      (fun n : ℕ => (32 * K) * (((n : ℝ) ^ tau8 η₀) ^ (10 / tau8 η₀) *
        Real.exp (-2 * (n : ℝ) ^ tau8 η₀))) atTop (nhds 0) := by
    simpa using hpolyTend.const_mul (32 * K)
  have hpolyEv : ∀ᶠ n : ℕ in atTop,
      (32 * K) * (((n : ℝ) ^ tau8 η₀) ^ (10 / tau8 η₀) *
        Real.exp (-2 * (n : ℝ) ^ tau8 η₀)) < 1 :=
    hpolyScaled.eventually (Iio_mem_nhds one_pos)
  have hall : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ (2 * h + 1) ≤ (n : ℝ) ^ (1 / 100 : ℝ) ∧
      100 ≤ Real.log (n : ℝ) ∧
      (h : ℝ) + 1 ≤ (n : ℝ) ^ (tau8 η₀ / 2) ∧
      (32 * K) * (((n : ℝ) ^ tau8 η₀) ^ (10 / tau8 η₀) *
        Real.exp (-2 * (n : ℝ) ^ tau8 η₀)) < 1 ∧ 1 ≤ n := by
    filter_upwards [hbaseEv, hlogEv, hhalfEv, hpolyEv, eventually_ge_atTop (1 : ℕ)]
      with n hnBase hnlog hnhalf hnpoly hn
    exact ⟨hnBase, hnlog, hnhalf, hnpoly, hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hall
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨hnBase, hnlog, hnhalf, hnpoly, hn1⟩ := hn₀ n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hsLower : (n : ℝ) ^ tau8 η₀ ≤ (sC η₀ n : ℝ) := by
    unfold sC
    exact Nat.le_ceil _
  have hsCeil : (sC η₀ n : ℝ) ≤ (n : ℝ) ^ tau8 η₀ + 1 := by
    unfold sC
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ tau8 η₀)).le
  have hbetaPow : (n : ℝ) ^ β ≤ (n : ℝ) ^ (tau8 η₀ / 2) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have hpositiveExp : h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2) ≤
      (n : ℝ) ^ tau8 η₀ := by
    have hhalfSq : ((n : ℝ) ^ (tau8 η₀ / 2)) ^ 2 = (n : ℝ) ^ tau8 η₀ := by
      calc
        ((n : ℝ) ^ (tau8 η₀ / 2)) ^ 2 =
            (n : ℝ) ^ (tau8 η₀ / 2) * (n : ℝ) ^ (tau8 η₀ / 2) := by ring
        _ = (n : ℝ) ^ ((tau8 η₀ / 2) + (tau8 η₀ / 2)) :=
          (Real.rpow_add hnpos _ _).symm
        _ = (n : ℝ) ^ tau8 η₀ := by congr 1 <;> ring
    have hhalfNonneg : 0 ≤ (n : ℝ) ^ (tau8 η₀ / 2) := by positivity
    calc
      h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2) ≤
          h * (n : ℝ) ^ (tau8 η₀ / 2) + (n : ℝ) ^ (tau8 η₀ / 2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hbetaPow (by positivity)) le_rfl
      _ = ((h : ℝ) + 1) * (n : ℝ) ^ (tau8 η₀ / 2) := by ring
      _ ≤ ((n : ℝ) ^ (tau8 η₀ / 2)) ^ 2 := by
        calc
          ((h : ℝ) + 1) * (n : ℝ) ^ (tau8 η₀ / 2) ≤
              (n : ℝ) ^ (tau8 η₀ / 2) * (n : ℝ) ^ (tau8 η₀ / 2) :=
            mul_le_mul_of_nonneg_right hnhalf hhalfNonneg
          _ = ((n : ℝ) ^ (tau8 η₀ / 2)) ^ 2 := by ring
      _ = (n : ℝ) ^ tau8 η₀ := hhalfSq
  have hpow2 : (2 : ℝ) ^ (2 * h + 1) = (2 : ℝ) ^ (2 * h) * 2 := by
    rw [pow_succ]
  have hbaseBound :
      ((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) * (2 : ℝ) ^ (2 * h) ≤
        (n : ℝ) ^ (-(3 / 100 : ℝ)) := by
    calc
      ((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) * (2 : ℝ) ^ (2 * h) =
          (2 : ℝ) ^ (2 * h + 1) * (n : ℝ) ^ (-(4 / 100 : ℝ)) := by rw [hpow2]; ring
      _ ≤ (n : ℝ) ^ (1 / 100 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_right hnBase (by positivity)
      _ = (n : ℝ) ^ (-(3 / 100 : ℝ)) := by
        rw [← Real.rpow_add hnpos]
        congr 1 <;> ring
  have hsPower :
      ((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ (sC η₀ n) *
          (2 : ℝ) ^ (h * (2 * sC η₀ n)) =
        (((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) * (2 : ℝ) ^ (2 * h)) ^
          (sC η₀ n) := by
    have hexp : h * (2 * sC η₀ n) = (2 * h) * sC η₀ n := by ring
    rw [hexp, pow_mul, ← mul_pow]
  have hpowerExp : ((n : ℝ) ^ (-(3 / 100 : ℝ))) ^ (sC η₀ n) =
      (n : ℝ) ^ ((-(3 / 100 : ℝ)) * (sC η₀ n : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  have hexpOrder : (-(3 / 100 : ℝ)) * (sC η₀ n : ℝ) ≤
      (-(3 / 100 : ℝ)) * (n : ℝ) ^ tau8 η₀ := by nlinarith [hsLower]
  have hpowerOrder : (n : ℝ) ^ ((-(3 / 100 : ℝ)) * (sC η₀ n : ℝ)) ≤
      (n : ℝ) ^ ((-(3 / 100 : ℝ)) * (n : ℝ) ^ tau8 η₀) :=
    Real.rpow_le_rpow_of_exponent_le hnR hexpOrder
  have ht : 0 ≤ (n : ℝ) ^ tau8 η₀ := by positivity
  have hlogMul : 100 * (n : ℝ) ^ tau8 η₀ ≤
      (n : ℝ) ^ tau8 η₀ * Real.log (n : ℝ) := by
    calc
      100 * (n : ℝ) ^ tau8 η₀ = (n : ℝ) ^ tau8 η₀ * 100 := by ring
      _ ≤ (n : ℝ) ^ tau8 η₀ * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnlog ht
  have hnegRpow : (n : ℝ) ^ ((-(3 / 100 : ℝ)) * (n : ℝ) ^ tau8 η₀) ≤
      Real.exp (-3 * (n : ℝ) ^ tau8 η₀) := by
    rw [Real.rpow_def_of_pos hnpos]
    apply Real.exp_le_exp.mpr
    nlinarith [hlogMul]
  have hbasePow :
      ((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ (sC η₀ n) *
          (2 : ℝ) ^ (h * (2 * sC η₀ n)) ≤ Real.exp (-3 * (n : ℝ) ^ tau8 η₀) := by
    calc
      _ = (((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) * (2 : ℝ) ^ (2 * h)) ^
            (sC η₀ n) := hsPower
      _ ≤ ((n : ℝ) ^ (-(3 / 100 : ℝ))) ^ (sC η₀ n) :=
        pow_le_pow_left₀ (by positivity) hbaseBound _
      _ = (n : ℝ) ^ ((-(3 / 100 : ℝ)) * (sC η₀ n : ℝ)) := hpowerExp
      _ ≤ (n : ℝ) ^ ((-(3 / 100 : ℝ)) * (n : ℝ) ^ tau8 η₀) := hpowerOrder
      _ ≤ Real.exp (-3 * (n : ℝ) ^ tau8 η₀) := hnegRpow
  have htPow : ((n : ℝ) ^ tau8 η₀) ^ (10 / tau8 η₀) = (n : ℝ) ^ (10 : ℕ) := by
    rw [← Real.rpow_mul hnpos.le]
    have hexp : tau8 η₀ * (10 / tau8 η₀) = 10 := by field_simp [ne_of_gt hτ]
    rw [hexp]
    exact Real.rpow_natCast (n : ℝ) 10
  have hcapSmall : (n : ℝ) * fGrid η₀ n * bcompCap η₀ β K h n ≤
      (32 * K) * (n : ℝ) ^ 10 * Real.exp (-2 * (n : ℝ) ^ tau8 η₀) := by
    unfold fGrid bcompCap
    have hnTen : (n : ℝ) * (n : ℝ) ^ (9 : ℕ) = (n : ℝ) ^ 10 := by
      rw [show (10 : ℕ) = 9 + 1 by omega, pow_succ]
      ring
    have hAlgebra :
        (n : ℝ) * ((n : ℝ) ^ (9 : ℕ) *
          ((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ (sC η₀ n)) *
          (32 * K * (2 : ℝ) ^ (h * (2 * sC η₀ n)) *
            Real.exp (h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2))) =
        (32 * K) * (n : ℝ) ^ 10 *
          (((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ (sC η₀ n) *
            (2 : ℝ) ^ (h * (2 * sC η₀ n))) *
          Real.exp (h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2)) := by
      calc
        _ = (32 * K) * ((n : ℝ) * (n : ℝ) ^ 9) *
              (((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ (sC η₀ n) *
                (2 : ℝ) ^ (h * (2 * sC η₀ n))) *
              Real.exp (h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2)) := by ring
        _ = _ := by rw [hnTen]
    rw [hAlgebra]
    calc
      (32 * K) * (n : ℝ) ^ 10 *
          (((2 : ℝ) * (n : ℝ) ^ (-(4 / 100 : ℝ))) ^ (sC η₀ n) *
            (2 : ℝ) ^ (h * (2 * sC η₀ n))) *
          Real.exp (h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2)) ≤
        (32 * K) * (n : ℝ) ^ 10 *
          Real.exp (-3 * (n : ℝ) ^ tau8 η₀) *
          Real.exp (h * (n : ℝ) ^ β + (n : ℝ) ^ (tau8 η₀ / 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbasePow (by positivity)) (by positivity)
      _ ≤ (32 * K) * (n : ℝ) ^ 10 *
          Real.exp (-3 * (n : ℝ) ^ tau8 η₀) *
          Real.exp ((n : ℝ) ^ tau8 η₀) := by
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hpositiveExp) (by positivity)
      _ = (32 * K) * (n : ℝ) ^ 10 *
          (Real.exp (-3 * (n : ℝ) ^ tau8 η₀) *
            Real.exp ((n : ℝ) ^ tau8 η₀)) := by ring
      _ = (32 * K) * (n : ℝ) ^ 10 *
          Real.exp (-2 * (n : ℝ) ^ tau8 η₀) := by
        have hExp : Real.exp (-3 * (n : ℝ) ^ tau8 η₀) *
            Real.exp ((n : ℝ) ^ tau8 η₀) = Real.exp (-2 * (n : ℝ) ^ tau8 η₀) := by
          calc
            Real.exp (-3 * (n : ℝ) ^ tau8 η₀) *
                Real.exp ((n : ℝ) ^ tau8 η₀) =
                Real.exp (-3 * (n : ℝ) ^ tau8 η₀ + (n : ℝ) ^ tau8 η₀) := by
              rw [← Real.exp_add]
            _ = Real.exp (-2 * (n : ℝ) ^ tau8 η₀) := by congr 1 <;> ring
        rw [hExp]
  have hnpoly : (32 * K) * (n : ℝ) ^ 10 *
      Real.exp (-2 * (n : ℝ) ^ tau8 η₀) < 1 := by
    simpa [htPow, mul_assoc] using hnpoly
  exact hcapSmall.trans hnpoly.le

private theorem one_sub_pow_lower (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * x ≤ (1 - x) ^ m := by
  have hpow_le_one : ∀ m : ℕ, (1 - x) ^ m ≤ 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        calc
          (1 - x) ^ m * (1 - x) ≤ 1 * (1 - x) :=
            mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hx1)
          _ ≤ 1 := by nlinarith
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      have hmul : x * (1 - x) ^ m ≤ x := by
        calc
          x * (1 - x) ^ m ≤ x * 1 :=
            mul_le_mul_of_nonneg_left (hpow_le_one m) hx0
          _ = x := by ring
      calc
        1 - ((m + 1 : ℕ) : ℝ) * x = (1 - (m : ℝ) * x) - x := by push_cast; ring
        _ ≤ (1 - x) ^ m - x := sub_le_sub_right ih x
        _ ≤ (1 - x) ^ m - x * (1 - x) ^ m := by linarith
        _ = (1 - x) ^ m * (1 - x) := by ring

private theorem bcompChargeSmall (η₀ cH : ℝ) (hη₀ : 0 < η₀) (hcH : 0 < cH) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      4 * Real.exp (-(n : ℝ) ^ cH) * (n : ℝ) *
        (1 + ((2 * sC η₀ n + 1) ^ 4 : ℕ)) ≤ 1 / 4 := by
  have hτ : 0 < tau8 η₀ := by rw [tau8_eq]; unfold eta8; positivity
  have hτlt : tau8 η₀ < 1 := by
    rw [tau8_eq]
    have hη8 : eta8 η₀ ≤ 4 / 100 := min_le_right _ _
    nlinarith
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ cH) atTop atTop :=
    (tendsto_rpow_atTop hcH).comp tendsto_natCast_atTop_atTop
  have hpoly : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ cH) ^ (5 / cH) * Real.exp (-(n : ℝ) ^ cH))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (5 / cH) 1 one_pos).comp htend
    simpa [Function.comp_def] using h
  have hscaled : Tendsto
      (fun n : ℕ => 2504 * (((n : ℝ) ^ cH) ^ (5 / cH) * Real.exp (-(n : ℝ) ^ cH)))
      atTop (nhds 0) := by simpa using hpoly.const_mul (2504 : ℝ)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2504 * (((n : ℝ) ^ cH) ^ (5 / cH) * Real.exp (-(n : ℝ) ^ cH)) < 1 / 4 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hτpow : (n : ℝ) ^ tau8 η₀ ≤ n :=
    by
      have hp := Real.rpow_le_rpow_of_exponent_le hnR hτlt.le
      simpa [Real.rpow_one] using hp
  have hs : (sC η₀ n : ℝ) ≤ (n : ℝ) + 1 := by
    unfold sC
    exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ tau8 η₀)).le.trans
      (by simpa [add_comm] using add_le_add_right hτpow 1)
  have hsNat : sC η₀ n ≤ n + 1 := by exact_mod_cast hs
  have hkey : (2 * sC η₀ n + 1 : ℕ) ≤ 5 * n := by
    omega
  have hpowkey : ((2 * sC η₀ n + 1 : ℕ) : ℝ) ^ 4 ≤ (5 * (n : ℝ)) ^ 4 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkey) 4
  have hdelta : (1 + ((2 * sC η₀ n + 1) ^ 4 : ℕ) : ℝ) ≤ 626 * (n : ℝ) ^ 4 := by
    have hcast : ((2 * sC η₀ n + 1) ^ 4 : ℕ) =
        ((2 * sC η₀ n + 1 : ℕ) : ℝ) ^ 4 := by norm_cast
    rw [hcast]
    calc
      1 + ((2 * sC η₀ n + 1 : ℕ) : ℝ) ^ 4 ≤ 1 + (5 * (n : ℝ)) ^ 4 :=
        by simpa [add_comm] using add_le_add_left hpowkey 1
      _ = 1 + 625 * (n : ℝ) ^ 4 := by norm_num; ring
      _ ≤ 626 * (n : ℝ) ^ 4 := by
        have hone : 1 ≤ (n : ℝ) ^ 4 := by
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hnR 4
        nlinarith
  have hM : (n : ℝ) *
      (1 + ((2 * sC η₀ n + 1) ^ 4 : ℕ)) ≤ 626 * (n : ℝ) ^ 5 := by
    calc
      _ ≤ (n : ℝ) * (626 * (n : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hdelta (by positivity)
      _ = 626 * (n : ℝ) ^ 5 := by rw [show (n : ℝ) ^ 5 = (n : ℝ) ^ 4 * n by ring]; ring
  have hten : ((n : ℝ) ^ cH) ^ (5 / cH) = (n : ℝ) ^ (5 : ℕ) := by
    rw [← Real.rpow_mul hnpos.le]
    have he : cH * (5 / cH) = 5 := by field_simp [ne_of_gt hcH]
    rw [he, ← Real.rpow_natCast]
    norm_num
  have hpolyN : 2504 * (n : ℝ) ^ 5 * Real.exp (-(n : ℝ) ^ cH) < 1 / 4 := by
    simpa [hten, mul_assoc] using hn₀ n hn0
  calc
    4 * Real.exp (-(n : ℝ) ^ cH) * (n : ℝ) *
        (1 + ((2 * sC η₀ n + 1) ^ 4 : ℕ)) ≤
      4 * Real.exp (-(n : ℝ) ^ cH) * (626 * (n : ℝ) ^ 5) := by
        have hmul := mul_le_mul_of_nonneg_left hM
          (by positivity : 0 ≤ 4 * Real.exp (-(n : ℝ) ^ cH))
        simpa [mul_assoc] using hmul
    _ = 2504 * (n : ℝ) ^ 5 * Real.exp (-(n : ℝ) ^ cH) := by ring
    _ ≤ 1 / 4 := hpolyN.le

private theorem bcomp_le_cap {η₀ γ β p K : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (X Y R : Finset (Fin D.N)) (hStd : Std D γ K X Y R) (hGF : GridFacts η₀ D.n)
    (Θ : D.Hist) (g : D.KeyT) (x : Fin D.N) (hbase : D.BaseGates Θ g) :
    D.Bcomp Θ g x ≤ bcompCap η₀ β K h D.n := by
  classical
  have hmix : ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) ≤
      Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * (4 * K) := by
    calc
      ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) ≤
          ∑ i, (Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * D.M.Λ i) *
            ((D.N : ℝ) * (D.M.μ i).w x) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hbase.1 i)
          (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
      _ = Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
            ((D.N : ℝ) * ∑ i, D.M.Λ i * (D.M.μ i).w x) := by
          calc
            ∑ i, Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * D.M.Λ i *
                ((D.N : ℝ) * (D.M.μ i).w x) =
                Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
                  ∑ i, D.M.Λ i * ((D.N : ℝ) * (D.M.μ i).w x) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            _ = Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
                  ((D.N : ℝ) * ∑ i, D.M.Λ i * (D.M.μ i).w x) := by
              congr 1
              calc
                ∑ i, D.M.Λ i * ((D.N : ℝ) * (D.M.μ i).w x) =
                    ∑ i, (D.N : ℝ) * (D.M.Λ i * (D.M.μ i).w x) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
                _ = (D.N : ℝ) * ∑ i, D.M.Λ i * (D.M.μ i).w x := by rw [Finset.mul_sum]
      _ ≤ Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * (4 * K) :=
          mul_le_mul_of_nonneg_left (hStd.bal.1 x) (by positivity)
  have hcard : h * (crossKeys g).card ≤ h * (2 * sC η₀ D.n) :=
    Nat.mul_le_mul_left h (hGF.crossKeys_card g)
  have hAGinv : (D.AG g)⁻¹ ≤ (2 : ℝ) ^ (h * (2 * sC η₀ D.n)) := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard
    simpa [Ctx.AG] using hp
  have hFnonneg : 0 ≤ ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (D.postW_nonneg _ _) (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
  have hAGpos : 0 < D.AG g := by unfold Ctx.AG; positivity
  have hscale : 0 ≤ 8 * (D.AG g)⁻¹ := by positivity
  have hB : D.Bcomp Θ g x ≤ 8 * (D.AG g)⁻¹ *
      (∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by
    unfold Ctx.Bcomp
    rw [if_pos hbase]
    by_cases hhit : D.crossHit Θ g x
    · simp [hhit]
    · simp [hhit]
      exact mul_nonneg hscale hFnonneg
  calc
    D.Bcomp Θ g x ≤ 8 * (D.AG g)⁻¹ *
        (∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := hB
    _ ≤ 8 * (2 : ℝ) ^ (h * (2 * sC η₀ D.n)) *
          (∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by
      have htemp : (D.AG g)⁻¹ *
          (∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) ≤
          (2 : ℝ) ^ (h * (2 * sC η₀ D.n)) *
          (∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) :=
        mul_le_mul_of_nonneg_right hAGinv hFnonneg
      have htemp' := mul_le_mul_of_nonneg_left htemp (by norm_num : (0 : ℝ) ≤ 8)
      simpa [mul_assoc] using htemp'
    _ ≤ 8 * (2 : ℝ) ^ (h * (2 * sC η₀ D.n)) *
          (Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * (4 * K)) :=
      mul_le_mul_of_nonneg_left hmix (by positivity)
    _ = bcompCap η₀ β K h D.n := by
      unfold bcompCap
      ring

private theorem bcomp_dep {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (g : D.KeyT) (x : Fin D.N) :
    FinProb.DependsOn (fun Θ => D.Bcomp Θ g x) (keyBall g 1) := by
  classical
  intro Θ Θ' hEq
  have hg : g ∈ keyBall g 1 := by
    unfold keyBall
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · simp [keyDist]
  have hown : Θ g = Θ' g := hEq g hg
  have hball (u : D.KeyT) (hu : u ∈ crossKeys g) : u ∈ keyBall g 1 := by
    unfold keyBall
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_univ _
    · have hdist := (Finset.mem_filter.mp hu).2
      omega
  have hcross (y : Fin D.N) (u : D.KeyT) (hu : u ∈ crossKeys g) :
      D.hitsAll y (Θ u) = D.hitsAll y (Θ' u) :=
    congrArg (D.hitsAll y) (hEq u (hball u hu))
  have hcrossHit (y : Fin D.N) : D.crossHit Θ g y = D.crossHit Θ' g y := by
    apply propext
    change (∀ u ∈ crossKeys g, D.hitsAll y (Θ u)) ↔
      (∀ u ∈ crossKeys g, D.hitsAll y (Θ' u))
    constructor
    · intro hh u hu
      rw [← hcross y u hu]
      exact hh u hu
    · intro hh u hu
      rw [hcross y u hu]
      exact hh u hu
  have hownhit (y : Fin D.N) : D.ownHit Θ g y = D.ownHit Θ' g y := by
    unfold Ctx.ownHit
    rw [hcrossHit y, congrArg (D.hitsAll y) hown]
  have hminus (i : D.M.ι) : D.dMinus Θ g i = D.dMinus Θ' g i := by
    unfold Ctx.dMinus
    apply Finset.sum_congr rfl
    intro y _
    rw [hcrossHit y]
  have hplus (i : D.M.ι) : D.dPlus Θ g i = D.dPlus Θ' g i := by
    unfold Ctx.dPlus
    apply Finset.sum_congr rfl
    intro y _
    rw [hownhit y]
  have homit (i : D.M.ι) (u₀ : D.KeyT) (hu₀ : u₀ ∈ crossKeys g) :
      D.dOmit Θ g u₀ i = D.dOmit Θ' g u₀ i := by
    unfold Ctx.dOmit
    apply Finset.sum_congr rfl
    intro y _
    have hprop : (∀ u ∈ (crossKeys g).erase u₀, D.hitsAll y (Θ u)) =
        (∀ u ∈ (crossKeys g).erase u₀, D.hitsAll y (Θ' u)) := by
      apply propext
      constructor
      · intro hh u hu
        have huCross : u ∈ crossKeys g := (Finset.mem_erase.mp hu).2
        rw [← hcross y u huCross]
        exact hh u hu
      · intro hh u hu
        have huCross : u ∈ crossKeys g := (Finset.mem_erase.mp hu).2
        rw [hcross y u huCross]
        exact hh u hu
    simp_rw [hprop]
  have hpost (i : D.M.ι) : D.postW (Θ g) i = D.postW (Θ' g) i := by rw [hown]
  have hgateOpen (i : D.M.ι) : D.GateOpen Θ g i = D.GateOpen Θ' g i := by
    simp [Ctx.GateOpen, hminus i, hplus i]
  have htilt (i : D.M.ι) : D.tiltW Θ g i = D.tiltW Θ' g i := by
    simp [Ctx.tiltW, hpost i, hminus i, hgateOpen i]
  have hZG : D.ZG Θ g = D.ZG Θ' g := by simp [Ctx.ZG, htilt]
  have hG1 : D.Gate1 Θ g ↔ D.Gate1 Θ' g := by simp [Ctx.Gate1, hpost]
  have hG2 : D.Gate2 Θ g ↔ D.Gate2 Θ' g := by simp [Ctx.Gate2, hZG]
  have hG34 : D.Gate34 Θ g ↔ D.Gate34 Θ' g := by
    unfold Ctx.Gate34
    constructor
    · rintro ⟨hη, hΛ, hrest⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hpost, hminus] using hη
      · simpa only [hminus] using hΛ
      · intro u hu
        obtain ⟨⟨hηlo, hηhi⟩, ⟨hΛlo, hΛhi⟩⟩ := hrest u hu
        simp_rw [homit _ u hu] at hηlo hηhi hΛlo hΛhi
        simp_rw [hpost] at hηlo hηhi
        exact ⟨⟨hηlo, hηhi⟩, ⟨hΛlo, hΛhi⟩⟩
    · rintro ⟨hη, hΛ, hrest⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [← hpost, ← hminus] using hη
      · simpa only [← hminus] using hΛ
      · intro u hu
        obtain ⟨⟨hηlo, hηhi⟩, ⟨hΛlo, hΛhi⟩⟩ := hrest u hu
        simp_rw [← homit _ u hu] at hηlo hηhi hΛlo hΛhi
        simp_rw [← hpost] at hηlo hηhi
        exact ⟨⟨hηlo, hηhi⟩, ⟨hΛlo, hΛhi⟩⟩
  have hbase : D.BaseGates Θ g = D.BaseGates Θ' g :=
    propext (and_congr hG1 (and_congr hG2 hG34))
  have hsum : (∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) =
      ∑ i, D.postW (Θ' g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hpost]
  simp [Ctx.Bcomp, hbase, hcrossHit x, hsum]

private theorem keyDist_symm {η₀ : ℝ} {n : ℕ} (a b : Key η₀ n) :
    keyDist a b = keyDist b a := by
  unfold keyDist
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.dist_comm _ _

private theorem keyDist_triangle {η₀ : ℝ} {n : ℕ} (a b c : Key η₀ n) :
    keyDist a c ≤ keyDist a b + keyDist b c := by
  unfold keyDist
  calc
    (∑ r, Nat.dist (a r).val (c r).val) ≤
        ∑ r, (Nat.dist (a r).val (b r).val + Nat.dist (b r).val (c r).val) := by
      apply Finset.sum_le_sum
      intro r _
      unfold Nat.dist
      omega
    _ = _ := by rw [Finset.sum_add_distrib]

private theorem keyBall_disjoint_of_far {η₀ : ℝ} {n : ℕ} (a b : Key η₀ n)
    (hfar : 2 < keyDist a b) : Disjoint (keyBall a 1) (keyBall b 1) := by
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  have hav : keyDist a v ≤ 1 := by simpa [keyBall] using hva
  have hbv : keyDist b v ≤ 1 := by simpa [keyBall] using hvb
  have htri := keyDist_triangle a v b
  have hsym := keyDist_symm b v
  omega

private theorem bcomp_nonneg {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (g : D.KeyT) (x : Fin D.N) : 0 ≤ D.Bcomp Θ g x := by
  have hcross : 0 ≤ if D.crossHit Θ g x then (1 : ℝ) else 0 := ind_nonneg _
  have hAG : 0 < D.AG g := by unfold Ctx.AG; positivity
  have hscale : 0 ≤ (8 : ℝ) * (D.AG g)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr hAG.le)
  have hsum : 0 ≤ ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (D.postW_nonneg _ _) (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
  unfold Ctx.Bcomp
  by_cases hBase : D.BaseGates Θ g
  · simp only [hBase, if_true]
    exact mul_nonneg (mul_nonneg hscale hcross) hsum
  · simp [hBase]

private def bcompScopeUnion {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) {m : ℕ}
    (roles : Fin m → EvenRole D.n) : Finset D.KeyT :=
  (Finset.univ : Finset (Fin m)).biUnion fun i => keyBall (keyOf η₀ (roles i).1) 1

private def bcompTouchedEvents {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) {m : ℕ}
    (roles : Fin m → EvenRole D.n) : Finset D.KeyT :=
  Finset.univ.filter fun a => ¬ Disjoint (keyBall a 2) (bcompScopeUnion D roles)

private theorem realLE_inst_eq : Real.instLE = Real.instPreorder.toLE := by
  ext a b
  rfl

private theorem bcomp_joint_of_cost {η₀ γ β p K : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (X Y R : Finset (Fin D.N)) (hStd : Std D γ K X Y R)
    (hBM : D.BcompMean K) (hGF : GridFacts η₀ D.n) (hCP : CondProductBound) (hK : 0 < K)
    (charge : ℝ) (hLLL : D.HiddenLLL charge) {m : ℕ}
    (roles : Fin m → EvenRole D.n) (x : Fin D.N)
    (hsep : ∀ i j : Fin m, j < i → roles i ∉ evenKeyNear η₀ 8 (roles j))
    (hcost : ((1 - charge) ^ (bcompTouchedEvents D roles).card)⁻¹ ≤ (2 : ℝ) ^ m) :
    D.hiddenLaw.expect (fun Θ => ∏ i : Fin m,
      D.Bcomp Θ (keyOf η₀ (roles i).1) x) ≤ (2 : ℝ) ^ m * (40 * K) ^ m := by
  classical
  let row : Fin m → D.Hist → ℝ := fun i Θ => D.Bcomp Θ (keyOf η₀ (roles i).1) x
  let scopes : Fin m → Finset D.KeyT := fun i => keyBall (keyOf η₀ (roles i).1) 1
  let U : Finset D.KeyT := bcompScopeUnion D roles
  let Φ : D.Hist → ℝ := fun Θ => ∏ i : Fin m, row i Θ
  have hrow_dep (i : Fin m) : FinProb.DependsOn (row i) (scopes i) := by
    simpa [row, scopes] using bcomp_dep D (keyOf η₀ (roles i).1) x
  have hscope_disjoint (i j : Fin m) (hij : i ≠ j) : Disjoint (scopes i) (scopes j) := by
    have hfar : 2 < keyDist (keyOf η₀ (roles i).1) (keyOf η₀ (roles j).1) := by
      by_cases hji : j < i
      · have hnot := hsep i j hji
        have hnotDist : ¬ keyDist (keyOf η₀ (roles i).1) (keyOf η₀ (roles j).1) ≤ 8 := by
          intro hle
          apply hnot
          simp [evenKeyNear, hle]
        omega
      · have hij' : i < j := by omega
        have hnot := hsep j i hij'
        have hnotDist : ¬ keyDist (keyOf η₀ (roles j).1) (keyOf η₀ (roles i).1) ≤ 8 := by
          intro hle
          apply hnot
          simp [evenKeyNear, hle]
        have hsym := keyDist_symm (keyOf η₀ (roles j).1) (keyOf η₀ (roles i).1)
        omega
    exact keyBall_disjoint_of_far _ _ hfar
  have hΦdep : FinProb.DependsOn Φ U := by
    intro Θ Θ' hEq
    dsimp [Φ]
    apply Finset.prod_congr rfl
    intro i hi
    apply hrow_dep i
    intro v hv
    exact hEq v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)
  have hΦnonneg (Θ : D.Hist) : 0 ≤ Φ Θ := by
    dsimp [Φ]
    apply Finset.prod_nonneg
    intro i hi
    exact bcomp_nonneg D Θ (keyOf η₀ (roles i).1) x
  have hmoment : (FinProb.pi (fun _ : D.KeyT => D.R')).expect Φ =
      ∏ i : Fin m, (FinProb.pi (fun _ : D.KeyT => D.R')).expect (row i) := by
    simpa [Φ, row, Ctx.rawHidden] using
      (pi_expect_prod_disjoint (fun _ : D.KeyT => D.R') Finset.univ row scopes
        hrow_dep hscope_disjoint)
  have hmean_product : (FinProb.pi (fun _ : D.KeyT => D.R')).expect Φ ≤ (40 * K) ^ m := by
    rw [hmoment]
    have hple :
        (∏ i : Fin m, (FinProb.pi (fun _ : D.KeyT => D.R')).expect (row i)) ≤
          ∏ i : Fin m, (40 * K : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact expect_nonneg _ (row i)
          (fun Θ => bcomp_nonneg D Θ (keyOf η₀ (roles i).1) x)
      · intro i hi
        simpa [row, Ctx.rawHidden] using hBM (keyOf η₀ (roles i).1) x
    simpa using hple
  have hfree : ∀ ω : D.Hist,
      ∑ a : (∀ v : U, D.Tup),
        (∏ v : U, D.R'.w (a v)) * Φ (glue U ω a) ≤ (40 * K) ^ m := by
    intro ω
    rw [pi_free_integral_eq (fun _ : D.KeyT => D.R') U Φ hΦdep ω]
    simpa [Ctx.rawHidden] using hmean_product
  have hlllp : LLLInput (fun _ : D.KeyT => D.R') (fun a Θ => D.HBad Θ a)
      (fun a => keyBall a 2) charge ((2 * sC η₀ D.n + 1) ^ 4) := by
    simpa [Ctx.HiddenLLL] using hLLL
  have hcond := hCP (fun _ : D.KeyT => D.R') (fun a Θ => D.HBad Θ a)
    (fun a => keyBall a 2) charge ((2 * sC η₀ D.n + 1) ^ 4) hlllp
  have hcondMoment : D.hiddenLaw.expect Φ ≤
      (((1 - charge) ^
          (Finset.univ.filter fun a : D.KeyT => ¬ Disjoint (keyBall a 2) U).card)⁻¹) *
        (40 * K) ^ m := by
    change (condOr D.rawHidden (fun Θ => ∀ a, ¬ D.HBad Θ a)).expect Φ ≤ _
    simpa [Ctx.rawHidden, U, scopes, bcompTouchedEvents, bcompScopeUnion] using
      hcond.2 U Φ hΦnonneg ((40 * K) ^ m) hfree
  have hcostRaw : @LE.le ℝ Real.instPreorder.toLE
      ((1 - charge) ^ (bcompTouchedEvents D roles).card)⁻¹ ((2 : ℝ) ^ m) := by
    rw [← realLE_inst_eq]
    exact hcost
  have hTouchedEq : bcompTouchedEvents D roles =
      Finset.univ.filter (fun a : D.KeyT => ¬ Disjoint (keyBall a 2) U) := by
    apply Finset.ext
    intro a
    simp only [bcompTouchedEvents, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hcostNorm :
      @LE.le ℝ Real.instPreorder.toLE
        (((1 - charge) ^ (Finset.univ.filter fun a : D.KeyT => ¬ Disjoint (keyBall a 2) U).card)⁻¹)
        ((2 : ℝ) ^ m) := by
    rw [← hTouchedEq]
    exact hcostRaw
  calc
    D.hiddenLaw.expect Φ ≤
        (((1 - charge) ^
          (Finset.univ.filter fun a : D.KeyT => ¬ Disjoint (keyBall a 2) U).card)⁻¹) *
          (40 * K) ^ m := hcondMoment
    _ ≤ (2 : ℝ) ^ m * (40 * K) ^ m := by
      exact mul_le_mul_of_nonneg_right
        hcostNorm (by positivity)

private theorem bcomp_touch_cost {η₀ γ β p K cH : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (hGF : GridFacts η₀ D.n) (hη₀ : 0 < η₀) (hcH : 0 < cH)
    (hLLL : D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH))) {m : ℕ}
    (roles : Fin m → EvenRole D.n) (hm : m ≤ D.n)
    (hchargeSmall : 4 * Real.exp (-(D.n : ℝ) ^ cH) * (D.n : ℝ) *
      (1 + ((2 * sC η₀ D.n + 1) ^ 4 : ℕ)) ≤ 1 / 4)
    (hsep : ∀ i j : Fin m, j < i → roles i ∉ evenKeyNear η₀ 8 (roles j)) :
    ((1 - 2 * Real.exp (-(D.n : ℝ) ^ cH)) ^ (bcompTouchedEvents D roles).card)⁻¹ ≤
      (2 : ℝ) ^ m := by
  classical
  change LLLInput (fun _ : D.KeyT => D.R') (fun a Θ => D.HBad Θ a)
      (fun a => keyBall a 2) (2 * Real.exp (-(D.n : ℝ) ^ cH))
      ((2 * sC η₀ D.n + 1) ^ 4) at hLLL
  let U : Finset D.KeyT := bcompScopeUnion D roles
  let T : Finset D.KeyT := bcompTouchedEvents D roles
  let scopes : Fin m → Finset D.KeyT := fun i => keyBall (keyOf η₀ (roles i).1) 1
  let Δ : ℕ := (2 * sC η₀ D.n + 1) ^ 4
  have hn0 : 1 ≤ D.n := hGF.pos.1
  have hnR : (1 : ℝ) ≤ D.n := by exact_mod_cast hn0
  have hs : (sC η₀ D.n : ℝ) ≤ (D.n : ℝ) + 1 := by
    have hτlt : tau8 η₀ < 1 := by
      rw [tau8_eq]
      have hη8 : eta8 η₀ ≤ 4 / 100 := min_le_right _ _
      nlinarith
    have hpow : (D.n : ℝ) ^ tau8 η₀ ≤ D.n := by
      have hh := Real.rpow_le_rpow_of_exponent_le hnR hτlt.le
      simpa [Real.rpow_one] using hh
    unfold sC
    have hceil := (Nat.ceil_lt_add_one (by positivity : 0 ≤ (D.n : ℝ) ^ tau8 η₀)).le
    calc
      (Nat.ceil ((D.n : ℝ) ^ tau8 η₀) : ℝ) ≤ (D.n : ℝ) ^ tau8 η₀ + 1 := hceil
      _ = 1 + (D.n : ℝ) ^ tau8 η₀ := by ring
      _ ≤ 1 + D.n := by
        calc
          1 + (D.n : ℝ) ^ tau8 η₀ = (D.n : ℝ) ^ tau8 η₀ + 1 := by ring
          _ ≤ (D.n : ℝ) + 1 := add_le_add_left hpow 1
          _ = 1 + D.n := by ring
      _ = (D.n : ℝ) + 1 := by ring
  have hsNat : sC η₀ D.n ≤ D.n + 1 := by exact_mod_cast hs
  have hkey : (2 * sC η₀ D.n + 1 : ℕ) ≤ 5 * D.n := by omega
  have hΔ : Δ + 1 ≤ 626 * D.n ^ 4 := by
    dsimp [Δ]
    have hpow : (2 * sC η₀ D.n + 1 : ℕ) ^ 4 ≤ (5 * D.n) ^ 4 :=
      Nat.pow_le_pow_left hkey 4
    have hn4 : 1 ≤ D.n ^ 4 := Nat.one_le_pow 4 D.n hn0
    calc
      (2 * sC η₀ D.n + 1) ^ 4 + 1 ≤ (5 * D.n) ^ 4 + 1 :=
        Nat.add_le_add_right hpow 1
      _ ≤ 626 * D.n ^ 4 := by
        have h5 : (5 * D.n) ^ 4 = 625 * D.n ^ 4 := by ring
        rw [h5]
        nlinarith
  have hTouched : T.card ≤ m * (1 + Δ) := by
    let nbr : Fin m → Finset D.KeyT := fun i =>
      insert (keyOf η₀ (roles i).1) (Finset.univ.filter fun a =>
        a ≠ keyOf η₀ (roles i).1 ∧
          ¬ Disjoint (keyBall (keyOf η₀ (roles i).1) 2) (keyBall a 2))
    have hsub : T ⊆ (Finset.univ : Finset (Fin m)).biUnion nbr := by
      intro a ha
      have hhit : ¬ Disjoint (keyBall a 2) U := (Finset.mem_filter.mp ha).2
      have hex : ∃ v, v ∈ keyBall a 2 ∧ v ∈ U := by
        by_contra hn
        apply hhit
        apply Finset.disjoint_left.mpr
        intro v hva hvU
        exact hn ⟨v, hva, hvU⟩
      obtain ⟨v, hva, hvU⟩ := hex
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hvU
      have hvi2 : v ∈ keyBall (keyOf η₀ (roles i).1) 2 := by
        have hd := (Finset.mem_filter.mp hvi).2
        unfold keyBall
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · omega
      have hinter : ¬ Disjoint (keyBall (keyOf η₀ (roles i).1) 2) (keyBall a 2) := by
        intro hd
        have hnot := (Finset.disjoint_left.mp hd) hvi2
        exact hnot hva
      by_cases heq : a = keyOf η₀ (roles i).1
      · subst a
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_insert_self _ _⟩
      · exact Finset.mem_biUnion.mpr ⟨i, hi,
          Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, ⟨heq, hinter⟩⟩))⟩
    have hnbr (i : Fin m) : (nbr i).card ≤ 1 + Δ := by
      dsimp [nbr]
      let Nbr : Finset D.KeyT := Finset.univ.filter fun a =>
        a ≠ keyOf η₀ (roles i).1 ∧
          ¬ Disjoint (keyBall (keyOf η₀ (roles i).1) 2) (keyBall a 2)
      have hIns : (insert (keyOf η₀ (roles i).1) Nbr).card ≤ Nbr.card + 1 :=
        Finset.card_insert_le _ _
      have hdegree : Nbr.card ≤ Δ := by
        simpa [Nbr, Δ] using hLLL.degree (keyOf η₀ (roles i).1)
      change (insert (keyOf η₀ (roles i).1) Nbr).card ≤ 1 + Δ
      omega
    calc
      T.card ≤ ((Finset.univ : Finset (Fin m)).biUnion nbr).card := Finset.card_le_card hsub
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin m)), (nbr i).card := Finset.card_biUnion_le
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin m)), (1 + Δ) :=
        Finset.sum_le_sum fun i hi => hnbr i
      _ = m * (1 + Δ) := by
        change (∑ i : Fin m, (1 + Δ)) = m * (1 + Δ)
        simp [Finset.sum_const, nsmul_eq_mul]
  have hmR : (m : ℝ) ≤ D.n := by exact_mod_cast hm
  have hΔR : (1 + (Δ : ℝ)) ≤ 626 * (D.n : ℝ) ^ 4 := by
    have hcast : (Δ : ℝ) + 1 ≤ 626 * (D.n : ℝ) ^ 4 := by exact_mod_cast hΔ
    nlinarith [hcast]
  have hTle : (T.card : ℝ) ≤ (D.n : ℝ) * (1 + (Δ : ℝ)) := by
    have hT : (T.card : ℝ) ≤ (m : ℝ) * (1 + (Δ : ℝ)) := by exact_mod_cast hTouched
    exact hT.trans (mul_le_mul_of_nonneg_right hmR (by positivity))
  have hMx : (T.card : ℝ) * (2 * Real.exp (-(D.n : ℝ) ^ cH)) ≤ 1 / 8 := by
    have hsm' : 4 * Real.exp (-(D.n : ℝ) ^ cH) * (D.n : ℝ) *
        (1 + (Δ : ℝ)) ≤ 1 / 4 := by
      simpa [Δ] using hchargeSmall
    calc
      (T.card : ℝ) * (2 * Real.exp (-(D.n : ℝ) ^ cH)) ≤
          ((D.n : ℝ) * (1 + (Δ : ℝ))) * (2 * Real.exp (-(D.n : ℝ) ^ cH)) :=
        mul_le_mul_of_nonneg_right hTle (by positivity)
      _ = (1 / 2 : ℝ) *
            (4 * Real.exp (-(D.n : ℝ) ^ cH) * (D.n : ℝ) * (1 + (Δ : ℝ))) := by ring
      _ ≤ 1 / 8 := by nlinarith [hsm']
  by_cases hm0 : m = 0
  · subst m
    simp [bcompTouchedEvents, bcompScopeUnion]
  · have hx0 : 0 ≤ 2 * Real.exp (-(D.n : ℝ) ^ cH) := by positivity
    have hx1 : 2 * Real.exp (-(D.n : ℝ) ^ cH) ≤ 1 := hLLL.x_lt_one.le
    have hbasePos : 0 < 1 - 2 * Real.exp (-(D.n : ℝ) ^ cH) := sub_pos.mpr hLLL.x_lt_one
    have hden : 1 - ((T.card : ℝ) * (2 * Real.exp (-(D.n : ℝ) ^ cH))) ≤
        (1 - 2 * Real.exp (-(D.n : ℝ) ^ cH)) ^ T.card :=
      one_sub_pow_lower _ hx0 hx1 T.card
    have hdenHalf : (1 / 2 : ℝ) ≤
        (1 - 2 * Real.exp (-(D.n : ℝ) ^ cH)) ^ T.card := by linarith [hden, hMx]
    have hcost2 : ((1 - 2 * Real.exp (-(D.n : ℝ) ^ cH)) ^ T.card)⁻¹ ≤ 2 := by
      have hp : 1 / ((1 - 2 * Real.exp (-(D.n : ℝ) ^ cH)) ^ T.card) ≤ 2 := by
        apply (div_le_iff₀ (pow_pos hbasePos _)).2
        nlinarith [hdenHalf]
      simpa [one_div] using hp
    have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ m := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmpos
      simpa using hp
    have hcostFin : ((1 - 2 * Real.exp (-(D.n : ℝ) ^ cH)) ^ T.card)⁻¹ ≤ (2 : ℝ) ^ m :=
      hcost2.trans htwo
    simpa [T, bcompTouchedEvents, bcompScopeUnion] using hcostFin

private theorem selected_level_eq {p : HDParams} (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hlegal : ∀ j, p.LegalAt P E v j)
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    p.height Sites P A E p.Rlong v = ℓ.2.val := by
  classical
  have hH : p.height Sites P A E p.Rlong v < p.H := by
    by_contra hh
    simp [HDParams.selection, HDParams.selectionAt, hh] at hsel
  let j : Fin (p.H + 1) := ⟨p.height Sites P A E p.Rlong v, by omega⟩
  have hsel' := hsel
  simp [HDParams.selection, HDParams.selectionAt, hH, j] at hsel'
  rcases hsel' with ⟨_, ⟨hne, hchosen⟩⟩
  let active : Finset p.Loc := (E v j).filter (fun z => A z = true)
  let priorities := active.image (p.priority τ (v, j))
  have hneP : priorities.Nonempty := by
    rcases hne with ⟨z, hz⟩
    exact ⟨p.priority τ (v, j) z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let q := priorities.min' hneP
  have hmem : ∃ z, z ∈ active ∧ p.priority τ (v, j) z = q :=
    Finset.mem_image.mp (Finset.min'_mem priorities hneP)
  have hchosen' : Classical.choose hmem = ℓ := by
    simpa [active, priorities, q, j] using hchosen
  rcases Classical.choose_spec hmem with ⟨ha, _⟩
  rw [hchosen'] at ha
  have hE : ℓ ∈ E v j := (Finset.mem_filter.mp ha).1
  have hlevel := (hlegal j).1 ℓ hE
  have hlevelVal := congrArg Fin.val hlevel.2.1
  simpa [j] using hlevelVal.symm

private theorem selected_eligible {p : HDParams} (Sites : p.Sites) (P A : p.Loc → Bool)
    (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    ℓ ∈ E v ⟨p.height Sites P A E p.Rlong v, by
      have hH : p.height Sites P A E p.Rlong v < p.H := by
        by_contra hh
        simp [HDParams.selection, HDParams.selectionAt, hh] at hsel
      omega⟩ := by
  classical
  have hH : p.height Sites P A E p.Rlong v < p.H := by
    by_contra hh
    simp [HDParams.selection, HDParams.selectionAt, hh] at hsel
  let j : Fin (p.H + 1) := ⟨p.height Sites P A E p.Rlong v, by omega⟩
  have hsel' := hsel
  simp [HDParams.selection, HDParams.selectionAt, hH, j] at hsel'
  rcases hsel' with ⟨_, ⟨hne, hchosen⟩⟩
  let active : Finset p.Loc := (E v j).filter (fun z => A z = true)
  let priorities := active.image (p.priority τ (v, j))
  have hneP : priorities.Nonempty := by
    rcases hne with ⟨z, hz⟩
    exact ⟨p.priority τ (v, j) z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let q := priorities.min' hneP
  have hmem : ∃ z, z ∈ active ∧ p.priority τ (v, j) z = q :=
    Finset.mem_image.mp (Finset.min'_mem priorities hneP)
  have hchosen' : Classical.choose hmem = ℓ := by
    simpa [active, priorities, q, j] using hchosen
  rcases Classical.choose_spec hmem with ⟨ha, _⟩
  rw [hchosen'] at ha
  have hE : ℓ ∈ E v j := (Finset.mem_filter.mp ha).1
  simpa [j] using hE

private theorem selected_present_of_local_legal {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsite : v ∈ Sites) (hlegal : p.Legal P E (p.domBall Sites v p.Rlong))
    (hsel : p.selection Sites P A E τ v = some ℓ) : P ℓ = true := by
  have hvdom : v ∈ p.domBall Sites v p.Rlong := by simp [HDParams.domBall, hsite]
  have hmem := selected_eligible Sites P A E τ v ℓ hsel
  have hlegalAt := (hlegal v hvdom ⟨p.height Sites P A E p.Rlong v, by
    have hH : p.height Sites P A E p.Rlong v < p.H := by
      by_contra hh
      simp [HDParams.selection, HDParams.selectionAt, hh] at hsel
    omega⟩).1 ℓ hmem
  exact hlegalAt.1

private theorem selected_location_within_ball {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsite : v ∈ Sites)
    (hlegal : p.Legal P E (p.domBall Sites v p.Rlong))
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    hammingDist ℓ.1 v ≤ p.r := by
  have hvdom : v ∈ p.domBall Sites v p.Rlong := by simp [HDParams.domBall, hsite]
  have hmem := selected_eligible Sites P A E τ v ℓ hsel
  have hH : p.height Sites P A E p.Rlong v < p.H := by
    by_contra hh
    simp [HDParams.selection, HDParams.selectionAt, hh] at hsel
  let j : Fin (p.H + 1) := ⟨p.height Sites P A E p.Rlong v, by omega⟩
  have hmem' : ℓ ∈ E v j := by simpa [j] using hmem
  have hparts := (hlegal v hvdom j).1 ℓ hmem'
  exact hparts.2.2

private noncomputable def selectedCenterTerm {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (e : D.CellT) (x : Fin D.N)
    (P : D.Pos) (t : D.Tags) (A : (hdP η₀ D.n).Loc → Bool)
    (τ : (hdP η₀ D.n).Ties) (ℓ : D.Loc) : ℝ :=
  let q : D.Pre := ((Θ, P), ((t, fun _ => A), fun _ => τ))
  if D.LocalLegal Θ P t e ∧ D.sel q e = some ℓ then
    (D.N : ℝ) * (D.anchorU Θ e.1 (t e.1 ℓ)).w x
  else 0

private theorem selLoad_sum {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (q : D.Pre) (e : D.CellT) (x : Fin D.N) :
    D.selLoad q e x =
      ∑ ℓ : D.Loc, if D.sel q e = some ℓ then
        (D.N : ℝ) * (D.anchorU q.1.1 e.1 (q.2.1.1 e.1 ℓ)).w x else 0 := by
  classical
  cases hsel : D.sel q e <;> simp [Ctx.selLoad, Ctx.selTag, hsel]

private theorem selectedCenterTerm_sum {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (e : D.CellT) (x : Fin D.N)
    (P : D.Pos) (t : D.Tags) (A : (hdP η₀ D.n).Loc → Bool)
    (τ : (hdP η₀ D.n).Ties) :
    (if D.LocalLegal Θ P t e then 1 else 0) *
        D.selLoad ((Θ, P), ((t, fun _ => A), fun _ => τ)) e x =
      ∑ ℓ : D.Loc, selectedCenterTerm D Θ e x P t A τ ℓ := by
  classical
  by_cases hlegal : D.LocalLegal Θ P t e
  · simp [selectedCenterTerm, hlegal, selLoad_sum]
  · simp [selectedCenterTerm, hlegal]

private theorem selected_level_of_local_legal {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsite : v ∈ Sites)
    (hlegal : p.Legal P E (p.domBall Sites v p.Rlong))
    (hsel : p.selection Sites P A E τ v = some ℓ) :
    p.height Sites P A E p.Rlong v = ℓ.2.val := by
  have hvdom : v ∈ p.domBall Sites v p.Rlong := by
    simp [HDParams.domBall, hsite]
  apply selected_level_eq Sites P A E τ v ℓ
  · intro j
    exact hlegal v hvdom j
  · exact hsel

private theorem selected_pos_height_of_local_legal {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsite : v ∈ Sites)
    (hlegal : p.Legal P E (p.domBall Sites v p.Rlong))
    (hsel : p.selection Sites P A E τ v = some ℓ) (hℓ : 0 < ℓ.2.val) :
    0 < p.height Sites P A E p.Rlong v := by
  rw [selected_level_of_local_legal Sites P A E τ v ℓ hsite hlegal hsel]
  exact hℓ

private theorem selected_zero_height_of_local_legal {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties) (v : CubeVertex p.d) (ℓ : p.Loc)
    (hsite : v ∈ Sites)
    (hlegal : p.Legal P E (p.domBall Sites v p.Rlong))
    (hsel : p.selection Sites P A E τ v = some ℓ) (hℓ : ℓ.2.val = 0) :
    p.height Sites P A E p.Rlong v = 0 := by
  rw [selected_level_of_local_legal Sites P A E τ v ℓ hsite hlegal hsel]
  exact hℓ

private def loadDiffSet {d : ℕ} (v u : CubeVertex d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def loadVertexOfDiff {d : ℕ} (v : CubeVertex d) (s : Finset (Fin d)) : CubeVertex d :=
  fun i => if i ∈ s then !(v i) else v i

private def loadDiffEquiv {d : ℕ} (v : CubeVertex d) : CubeVertex d ≃ Finset (Fin d) where
  toFun := loadDiffSet v
  invFun := loadVertexOfDiff v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [loadVertexOfDiff, loadDiffSet, hi]
    · have hmem : i ∈ loadDiffSet v u := by simp [loadDiffSet, hi]
      have hbool : v i = !(u i) := by
        cases hu : u i <;> cases hv : v i <;> simp_all
      simp [loadVertexOfDiff, hmem, hbool]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s
    · simp [loadDiffSet, loadVertexOfDiff, hi]
    · simp [loadDiffSet, loadVertexOfDiff, hi]

private theorem loadDiffSet_card {d : ℕ} (v u : CubeVertex d) :
    (loadDiffSet v u).card = hammingDist u v := by
  simp [loadDiffSet, hammingDist, ne_comm]

private def loadBallToSubsets {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨loadDiffSet v u.1, by rw [loadDiffSet_card]; exact u.2⟩
  invFun s := ⟨loadVertexOfDiff v s.1, by
    rw [← loadDiffSet_card]
    simp [loadDiffSet, loadVertexOfDiff]
    exact s.2⟩
  left_inv := by intro u; apply Subtype.ext; exact (loadDiffEquiv v).left_inv u.1
  right_inv := by intro s; apply Subtype.ext; exact (loadDiffEquiv v).right_inv s.1

private def loadSmallSubsetFiberEquiv (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by simpa using congrArg Fin.val s.2⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by apply Fin.ext; exact s.2⟩
  left_inv := by intro s; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro s; apply Subtype.ext; rfl

private def loadSubsetsSmallEquiv (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) :=
    fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (loadSmallSubsetFiberEquiv d r))

private theorem loadCardSmallSubsets (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (loadSubsetsSmallEquiv d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem loadHammingBallCard (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => hammingDist u v ≤ r))
  exact hcard.symm.trans
    ((Fintype.card_congr (loadBallToSubsets v)).trans (loadCardSmallSubsets d r))

private def loadLevelBallEquiv (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
    {u : CubeVertex d // hammingDist u v ≤ r} ≃
      {ℓ : CubeVertex d × Fin (H + 1) // ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r} where
  toFun u := ⟨(u.1, j), by simp [u.2]⟩
  invFun ℓ := ⟨ℓ.1.1, ℓ.2.2⟩
  left_inv := by intro u; apply Subtype.ext; rfl
  right_inv := by
    intro ℓ
    rcases ℓ with ⟨⟨u, k⟩, ⟨hk, hdist⟩⟩
    apply Subtype.ext
    exact Prod.ext rfl hk.symm

private theorem loadLevelBallCard (d H r : ℕ) (j : Fin (H + 1)) (v : CubeVertex d) :
    (Finset.univ.filter (fun ℓ : CubeVertex d × Fin (H + 1) =>
      ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  calc
    (Finset.univ.filter (fun ℓ : CubeVertex d × Fin (H + 1) =>
      ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r)).card =
        Fintype.card {ℓ : CubeVertex d × Fin (H + 1) // ℓ.2 = j ∧ hammingDist ℓ.1 v ≤ r} := by
          symm
          exact Fintype.card_subtype _
    _ = Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} :=
          Fintype.card_congr (loadLevelBallEquiv d H r j v).symm
    _ = (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card :=
          Fintype.card_subtype _
    _ = _ := loadHammingBallCard d r v

private theorem bernoulli_forced_expect {α : Type*} [Fintype α] [DecidableEq α]
    (q : ℝ) (a : α) (f : (α → Bool) → ℝ) :
    (FinProb.pi (fun _ : α => FinProb.bernoulli q)).expect
        (fun P => if P a then f P else 0) =
      (max 0 (min q 1)) *
        (FinProb.pi (fun z : α => if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q)).expect f := by
  classical
  let q' : ℝ := max 0 (min q 1)
  have hrest (P : α → Bool) :
      (∏ z ∈ Finset.univ.erase a, (FinProb.bernoulli q).w (P z)) =
        ∏ z ∈ Finset.univ.erase a,
          (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z) := by
    apply Finset.prod_congr rfl
    intro z hz
    have hza : z ≠ a := (Finset.mem_erase.mp hz).1
    by_cases haz : a = z
    · exact False.elim (hza haz.symm)
    · simp [haz]
  have hweight (P : α → Bool) :
      (∏ z, (FinProb.bernoulli q).w (P z)) * (if P a then (1 : ℝ) else 0) =
        q' * ∏ z, (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z) := by
    by_cases ha : P a
    · have hleft := Finset.mul_prod_erase (Finset.univ : Finset α)
        (fun z => (FinProb.bernoulli q).w (P z)) (Finset.mem_univ a)
      have hright := Finset.mul_prod_erase (Finset.univ : Finset α)
        (fun z => (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z))
        (Finset.mem_univ a)
      rw [← hleft, ← hright, hrest P]
      simp [ha, q', FinProb.bernoulli]
    · have hleft := Finset.mul_prod_erase (Finset.univ : Finset α)
        (fun z => (FinProb.bernoulli q).w (P z)) (Finset.mem_univ a)
      have hright := Finset.mul_prod_erase (Finset.univ : Finset α)
        (fun z => (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z))
        (Finset.mem_univ a)
      rw [← hleft, ← hright]
      simp [ha, FinProb.bernoulli]
  unfold FinProb.expect FinProb.pi
  calc
    (∑ P, (∏ z, (FinProb.bernoulli q).w (P z)) * (if P a then f P else 0)) =
        ∑ P, (q' * ∏ z, (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z)) * f P := by
          apply Finset.sum_congr rfl
          intro P _
          calc
            (∏ z, (FinProb.bernoulli q).w (P z)) * (if P a then f P else 0) =
                ((∏ z, (FinProb.bernoulli q).w (P z)) * (if P a then (1 : ℝ) else 0)) * f P := by
                  by_cases ha : P a <;> simp [ha] <;> ring
            _ = (q' * ∏ z, (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z)) * f P := by
                  rw [hweight P]
            _ = _ := by ring
    _ = q' * ∑ P, (∏ z, (if a = z then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P z)) * f P := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro P _
          ring

private theorem prod_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α → β → ℝ) :
    (FinProb.prod P Q).expect (fun ab => f ab.1 ab.2) =
      P.expect (fun a => Q.expect (f a)) := by
  classical
  unfold FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem prod_swap_expect {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : β → α → ℝ) :
    (FinProb.prod P Q).expect (fun ab => f ab.2 ab.1) =
      (FinProb.prod Q P).expect (fun ab => f ab.1 ab.2) := by
  calc
    (FinProb.prod P Q).expect (fun ab => f ab.2 ab.1) =
        P.expect (fun a => Q.expect (fun b => f b a)) :=
      prod_expect P Q (fun a b => f b a)
    _ = Q.expect (fun b => P.expect (fun a => f b a)) := by
      unfold FinProb.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (FinProb.prod Q P).expect (fun ab => f ab.1 ab.2) :=
      (prod_expect Q P (fun b a => f b a)).symm

private theorem prod_expect_assoc {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (P : FinProb α) (Q : FinProb β) (R : FinProb γ) (f : α → β → γ → ℝ) :
    (FinProb.prod (FinProb.prod P Q) R).expect
        (fun z => f z.1.1 z.1.2 z.2) =
      (FinProb.prod P (FinProb.prod Q R)).expect
        (fun z => f z.1 z.2.1 z.2.2) := by
  calc
    (FinProb.prod (FinProb.prod P Q) R).expect
        (fun z => f z.1.1 z.1.2 z.2) =
      (FinProb.prod P Q).expect (fun ab => R.expect (fun c => f ab.1 ab.2 c)) :=
        prod_expect (FinProb.prod P Q) R (fun ab c => f ab.1 ab.2 c)
    _ = P.expect (fun a => Q.expect (fun b => R.expect (fun c => f a b c))) := by
      exact prod_expect P Q (fun a b => R.expect (fun c => f a b c))
    _ = P.expect (fun a => (FinProb.prod Q R).expect (fun bc => f a bc.1 bc.2)) := by
      congr 1
      funext a
      exact (prod_expect Q R (f a)).symm
    _ = (FinProb.prod P (FinProb.prod Q R)).expect
        (fun z => f z.1 z.2.1 z.2.2) :=
      (prod_expect P (FinProb.prod Q R) (fun a bc => f a bc.1 bc.2)).symm

private theorem lane_pi_weight_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (ω : ∀ i, Ω i) :
    (∏ i, (P i).w (ω i)) =
      (∏ i : {i // i ∈ s}, (P i.1).w (ω i.1)) *
        (∏ i : {i // i ∉ s}, (P i.1).w (ω i.1)) := by
  classical
  let f : ι → ℝ := fun i => (P i).w (ω i)
  let t : Finset ι := Finset.univ.filter fun i => i ∉ s
  have hs : (∏ i : {i // i ∈ s}, f i.1) = ∏ i ∈ Finset.univ with i ∈ s, f i := by
    rw [Finset.univ_eq_attach]
    simpa [f] using Finset.prod_attach s f
  let ecomp : {i // i ∉ s} ≃ {i // i ∈ t} := {
    toFun := fun i => ⟨i.1, by simp [t, i.2]⟩
    invFun := fun i => ⟨i.1, (Finset.mem_filter.mp i.2).2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl }
  have hnot : (∏ i : {i // i ∉ s}, f i.1) =
      ∏ i ∈ Finset.univ with i ∉ s, f i := by
    calc
      (∏ i : {i // i ∉ s}, f i.1) = ∏ i : {i // i ∈ t}, f i.1 :=
        Fintype.prod_equiv ecomp _ _ (by intro i; rfl)
      _ = ∏ i ∈ t.attach, f i.1 := by rw [Finset.univ_eq_attach]
      _ = ∏ i ∈ t, f i := Finset.prod_attach t f
      _ = ∏ i ∈ Finset.univ with i ∉ s, f i := by simp [t]
  calc
    (∏ i, f i) =
        (∏ i ∈ Finset.univ with i ∈ s, f i) *
          (∏ i ∈ Finset.univ with i ∉ s, f i) :=
      (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : ι => i ∈ s) f).symm
    _ = (∏ i : {i // i ∈ s}, f i.1) * (∏ i : {i // i ∉ s}, f i.1) := by
      rw [← hs, ← hnot]

private theorem lane_pi_expect_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (P : ∀ i, FinProb (Ω i))
    (s : Finset ι) (f : (∀ i, Ω i) → ℝ) :
    (FinProb.pi P).expect f =
      ∑ a : (∀ i : {i // i ∈ s}, Ω i.1),
        ∑ b : (∀ i : {i // i ∉ s}, Ω i.1),
          (FinProb.pi (fun i : {i // i ∈ s} => P i.1)).w a *
            (FinProb.pi (fun i : {i // i ∉ s} => P i.1)).w b *
              f ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω).symm (a, b)) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) Ω
  change (∑ ω, (∏ i, (P i).w (ω i)) * f ω) = _
  rw [← Equiv.sum_comp e.symm (fun ω => (∏ i, (P i).w (ω i)) * f ω)]
  rw [Fintype.sum_prod_type]
  apply Fintype.sum_congr
  intro a
  apply Fintype.sum_congr
  intro b
  rw [lane_pi_weight_split P s (e.symm (a, b))]
  change ((∏ i : {i // i ∈ s}, (P i.1).w (e.symm (a, b) i.1)) *
      (∏ i : {i // i ∉ s}, (P i.1).w (e.symm (a, b) i.1))) * f (e.symm (a, b)) = _
  have hleft : ∀ i : {i // i ∈ s}, e.symm (a, b) i.1 = a i := by
    intro i
    simp [e, Equiv.piEquivPiSubtypeProd]
  have hright : ∀ i : {i // i ∉ s}, e.symm (a, b) i.1 = b i := by
    intro i
    simp only [e, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg i.2]
  simp_rw [hleft, hright]
  rfl

private theorem posLaw_forced_split {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (g : D.KeyT) (ℓ : D.Loc) (f : D.Pos → ℝ) :
    D.posLaw.expect (fun P => if P g ℓ then f P else 0) =
      (max 0 (min ((hdP η₀ D.n).lam / ((hdP η₀ D.n).V : ℝ)) 1)) *
        (FinProb.prod
          (FinProb.pi (fun _ : {k : D.KeyT // k ∉ ({g} : Finset D.KeyT)} =>
            (hdP η₀ D.n).posLaw))
          ((hdP η₀ D.n).posLawForced (some ℓ))).expect
            (fun z => f (reconstructPos D g z.2 z.1)) := by
  classical
  let p := hdP η₀ D.n
  let s : Finset D.KeyT := {g}
  let Q : D.KeyT → FinProb (D.Loc → Bool) := fun _ => p.posLaw
  let OLaw : FinProb (PosOutside D g) := FinProb.pi fun _ => p.posLaw
  let Eout := Equiv.piEquivPiSubtypeProd (fun k : D.KeyT => k ∈ s) (fun _ => D.Loc → Bool)
  let inner : (∀ k : {k // k ∈ s}, D.Loc → Bool) ≃ (D.Loc → Bool) :=
    singletonPiEquiv (β := D.Loc → Bool) g
  let q : ℝ := max 0 (min (p.lam / (p.V : ℝ)) 1)
  have hsplit := lane_pi_expect_split Q s (fun P => if P g ℓ then f P else 0)
  have hsplit' : D.posLaw.expect (fun P => if P g ℓ then f P else 0) =
      ∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
        ∑ b : PosOutside D g,
          (FinProb.pi (fun k : {k // k ∈ s} => Q k.1)).w a *
            (FinProb.pi (fun k : {k // k ∉ s} => Q k.1)).w b *
              (if (Eout.symm (a, b) g) ℓ then f (Eout.symm (a, b)) else 0) := by
    change (FinProb.pi Q).expect (fun P => if P g ℓ then f P else 0) = _
    exact hsplit
  have hrec (P : D.Loc → Bool) (O : PosOutside D g) :
      reconstructPos D g P O g = P := by
    unfold reconstructPos
    change (if h : g = g then P else _) = P
    simp
  have hEqEval (a : ∀ k : {k // k ∈ s}, D.Loc → Bool) (b : PosOutside D g) :
      Eout.symm (a, b) = reconstructPos D g (inner a) b := by
    funext k
    by_cases hk : k = g
    · subst k
      simp [Eout, reconstructPos, inner, s, singletonPiEquiv]
    · simp [Eout, reconstructPos, inner, s, hk, singletonPiEquiv]
  have hcentral (b : PosOutside D g) :
      (∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
        (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a *
          (if (inner a) ℓ then f (reconstructPos D g (inner a) b) else 0)) =
        q * ((p.posLawForced (some ℓ)).expect
          (fun P => f (reconstructPos D g P b))) := by
    have hExpect :
        (∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
          (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a *
            (if (inner a) ℓ then f (reconstructPos D g (inner a) b) else 0)) =
          (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).expect
            (fun a => if (inner a) ℓ then f (reconstructPos D g (inner a) b) else 0) := by
      rfl
    rw [hExpect, singletonSubtype_expect]
    have hBern := bernoulli_forced_expect (q := p.lam / (p.V : ℝ)) ℓ
      (fun P => f (reconstructPos D g P b))
    simp only [inner, Equiv.apply_symm_apply]
    simpa [p, q, HDParams.posLaw, HDParams.posLawForced] using hBern
  calc
    D.posLaw.expect (fun P => if P g ℓ then f P else 0) =
        ∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
          ∑ b : PosOutside D g,
            (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a * OLaw.w b *
              (if (Eout.symm (a, b) g) ℓ then f (Eout.symm (a, b)) else 0) := hsplit'
    _ = ∑ b : PosOutside D g,
          OLaw.w b * ∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
            (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a *
              (if (inner a) ℓ then f (reconstructPos D g (inner a) b) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        calc
          (∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
              (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a * OLaw.w b *
                (if (Eout.symm (a, b) g) ℓ then f (Eout.symm (a, b)) else 0)) =
              ∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
                OLaw.w b * ((FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a *
                  (if (inner a) ℓ then f (reconstructPos D g (inner a) b) else 0)) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [hEqEval a b, hrec]
            ring
          _ = OLaw.w b * ∑ a : (∀ k : {k // k ∈ s}, D.Loc → Bool),
                (FinProb.pi (fun k : {k // k ∈ s} => p.posLaw)).w a *
                  (if (inner a) ℓ then f (reconstructPos D g (inner a) b) else 0) := by
            symm
            rw [Finset.mul_sum]
    _ = ∑ b : PosOutside D g, OLaw.w b *
          (q * ((p.posLawForced (some ℓ)).expect
            (fun P => f (reconstructPos D g P b)))) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [hcentral b]
    _ = q * (FinProb.prod OLaw (p.posLawForced (some ℓ))).expect
          (fun z => f (reconstructPos D g z.2 z.1)) := by
        have hprod := prod_expect OLaw (p.posLawForced (some ℓ))
          (fun b P => f (reconstructPos D g P b))
        calc
          (∑ b : PosOutside D g, OLaw.w b *
              (q * (p.posLawForced (some ℓ)).expect
                (fun P => f (reconstructPos D g P b)))) =
              q * ∑ b : PosOutside D g, OLaw.w b *
                (p.posLawForced (some ℓ)).expect (fun P => f (reconstructPos D g P b)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
          _ = q * OLaw.expect (fun b => (p.posLawForced (some ℓ)).expect
                (fun P => f (reconstructPos D g P b))) := by
            have hE : OLaw.expect (fun b => (p.posLawForced (some ℓ)).expect
                (fun P => f (reconstructPos D g P b))) =
                ∑ b : PosOutside D g, OLaw.w b *
                  (p.posLawForced (some ℓ)).expect
                    (fun P => f (reconstructPos D g P b)) := rfl
            rw [← hE]
          _ = q * (FinProb.prod OLaw (p.posLawForced (some ℓ))).expect
                (fun z => f (reconstructPos D g z.2 z.1)) := by rw [← hprod]

private theorem rawTAT_expect_at_key {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (g : D.KeyT)
    (f : (D.Loc → D.M.ι) → ((hdP η₀ D.n).Loc → Bool) → (hdP η₀ D.n).Ties → ℝ) :
    (D.rawTAT Θ).expect (fun ω => f (ω.1.1 g) (ω.1.2 g) (ω.2 g)) =
      (D.tagLawAll Θ).expect (fun t =>
        D.actLaw.expect (fun A => D.tieLaw.expect (fun τ => f (t g) (A g) (τ g)))) := by
  classical
  unfold Ctx.rawTAT
  calc
    (((D.tagLawAll Θ).prod D.actLaw).prod D.tieLaw).expect
        (fun ω => f (ω.1.1 g) (ω.1.2 g) (ω.2 g)) =
      ((D.tagLawAll Θ).prod D.actLaw).expect
        (fun z => D.tieLaw.expect (fun τ => f (z.1 g) (z.2 g) (τ g))) := by
          exact prod_expect ((D.tagLawAll Θ).prod D.actLaw) D.tieLaw
            (fun z τ => f (z.1 g) (z.2 g) (τ g))
    _ = (D.tagLawAll Θ).expect
        (fun t => D.actLaw.expect (fun A => D.tieLaw.expect (fun τ => f (t g) (A g) (τ g)))) := by
          exact prod_expect (D.tagLawAll Θ) D.actLaw
            (fun t A => D.tieLaw.expect (fun τ => f (t g) (A g) (τ g)))
    _ = _ := by rfl

private theorem rawTAT_expect_local_slices {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) (g : D.KeyT)
    (f : D.Tags → ((hdP η₀ D.n).Loc → Bool) → (hdP η₀ D.n).Ties → ℝ) :
    (D.rawTAT Θ).expect (fun ω => f ω.1.1 (ω.1.2 g) (ω.2 g)) =
      (D.tagLawAll Θ).expect (fun t =>
        (hdP η₀ D.n).actLaw.expect (fun A =>
          (hdP η₀ D.n).tieLaw.expect (fun τ => f t A τ))) := by
  classical
  let p₀ := hdP η₀ D.n
  unfold Ctx.rawTAT
  calc
    (((D.tagLawAll Θ).prod D.actLaw).prod D.tieLaw).expect
        (fun ω => f ω.1.1 (ω.1.2 g) (ω.2 g)) =
      (D.tagLawAll Θ).expect (fun t => D.actLaw.expect (fun A =>
        D.tieLaw.expect (fun τ => f t (A g) (τ g)))) := by
          calc
            (((D.tagLawAll Θ).prod D.actLaw).prod D.tieLaw).expect
                (fun ω => f ω.1.1 (ω.1.2 g) (ω.2 g)) =
              ((D.tagLawAll Θ).prod D.actLaw).expect (fun z =>
                D.tieLaw.expect (fun τ => f z.1 (z.2 g) (τ g))) :=
                  prod_expect ((D.tagLawAll Θ).prod D.actLaw) D.tieLaw
                    (fun z τ => f z.1 (z.2 g) (τ g))
            _ = (D.tagLawAll Θ).expect (fun t => D.actLaw.expect (fun A =>
                D.tieLaw.expect (fun τ => f t (A g) (τ g)))) :=
                  prod_expect (D.tagLawAll Θ) D.actLaw
                    (fun t A => D.tieLaw.expect (fun τ => f t (A g) (τ g)))
    _ = (D.tagLawAll Θ).expect (fun t => p₀.actLaw.expect (fun A =>
        p₀.tieLaw.expect (fun τ => f t A τ))) := by
          apply expect_congr
          intro t
          have hτ' (A : D.Acts) : D.tieLaw.expect (fun τ => f t (A g) (τ g)) =
              p₀.tieLaw.expect (fun τ => f t (A g) τ) := by
            have hτ := pi_singleton_expect
              (fun _ : D.KeyT => p₀.tieLaw) g (fun τ => f t (A g) τ)
            simpa [Ctx.tieLaw, p₀] using hτ
          have hA := pi_singleton_expect
            (fun _ : D.KeyT => p₀.actLaw) g (fun a => p₀.tieLaw.expect (fun τ => f t a τ))
          have hA' : D.actLaw.expect (fun A => p₀.tieLaw.expect (fun τ => f t (A g) τ)) =
              p₀.actLaw.expect (fun a => p₀.tieLaw.expect (fun τ => f t a τ)) := by
            simpa [Ctx.actLaw, p₀] using hA
          calc
            D.actLaw.expect (fun A => D.tieLaw.expect (fun τ => f t (A g) (τ g))) =
                D.actLaw.expect (fun A => p₀.tieLaw.expect (fun τ => f t (A g) τ)) := by
                  apply expect_congr
                  intro A
                  exact hτ' A
            _ = p₀.actLaw.expect (fun a => p₀.tieLaw.expect (fun τ => f t a τ)) := hA'

private noncomputable def weightedLaw {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (m : ℝ) (hm : 0 < m) (hmEq : P.expect w = m) : FinProb Ω where
  w ω := P.w ω * w ω / m
  nonneg ω := div_nonneg (mul_nonneg (P.nonneg ω) (hw ω)) hm.le
  sum_eq_one := by
    rw [← Finset.sum_div]
    have hsum : (∑ ω, P.w ω * w ω) = m := by
      simpa [FinProb.expect] using hmEq
    rw [hsum]
    exact div_self hm.ne'

private theorem weightedLaw_expect {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (m : ℝ) (hm : 0 < m) (hmEq : P.expect w = m) (f : Ω → ℝ) :
    P.expect (fun ω => w ω * f ω) =
      m * (weightedLaw P w hw m hm hmEq).expect f := by
  classical
  unfold FinProb.expect weightedLaw
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  field_simp [hm.ne']

private theorem tilt_anchor_mass {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (g : D.KeyT) (x : Fin D.N)
    (hbase : D.BaseGates Θ g) (hΔ : D.Δ ≤ 1 / 4) :
    (D.tilt Θ g).expect (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x) ≤
      D.Bcomp Θ g x / 4 := by
  classical
  have hAG : 0 < D.AG g := by unfold Ctx.AG; positivity
  have hZlow : (4 / 5 : ℝ) * D.AG g ≤ D.ZG Θ g := by
    have hh := hbase.2.1.1
    nlinarith [hh]
  have hZ : 0 < D.ZG Θ g := lt_of_lt_of_le (mul_pos (by norm_num) hAG) hZlow
  have hInvZ : (D.ZG Θ g)⁻¹ ≤ ((4 / 5 : ℝ) * D.AG g)⁻¹ :=
    (inv_le_inv₀ hZ (mul_pos (by norm_num) hAG)).mpr hZlow
  have hDelta : 0 ≤ 1 - D.Δ := by linarith
  have hDeltaLow : (3 / 4 : ℝ) ≤ 1 - D.Δ := by linarith
  have hCrossTerm : ∀ i : D.M.ι,
      (D.tilt Θ g).w i * ((D.N : ℝ) * (D.anchorU Θ g i).w x) ≤
        (5 / (3 * D.AG g)) * (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) *
          (if D.crossHit Θ g x then 1 else 0) := by
    intro i
    have hpost : 0 ≤ D.postW (Θ g) i := D.postW_nonneg _ _
    have hminus : 0 ≤ D.dMinus Θ g i := D.dMinus_nonneg _ _ _
    have htiltLaw : (D.tilt Θ g).w i = D.tiltW Θ g i / D.ZG Θ g := by
      unfold Ctx.tilt
      change (if (∑ j, D.tiltW Θ g j) = 0 then D.tagLaw.w i else
        D.tiltW Θ g i / (∑ j, D.tiltW Θ g j)) = _
      have htotalPos : 0 < ∑ j, D.tiltW Θ g j := by simpa [Ctx.ZG] using hZ
      simp [Ctx.ZG, ne_of_gt htotalPos]
    by_cases hwi : D.tiltW Θ g i = 0
    · have hS : (D.tilt Θ g).w i = 0 := by rw [htiltLaw, hwi]; simp
      rw [hS]
      have hR : 0 ≤ (5 / (3 * D.AG g)) *
          (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) *
            (if D.crossHit Θ g x then 1 else 0) := by
        apply mul_nonneg
        · apply mul_nonneg
          · exact div_nonneg (by norm_num) (by positivity)
          · exact mul_nonneg hpost (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
        · exact ind_nonneg _
      simpa using hR
    · have hwiPos : 0 < D.tiltW Θ g i := lt_of_le_of_ne (D.tiltW_nonneg Θ g i) (Ne.symm hwi)
      have hopen : D.GateOpen Θ g i := by
        by_contra hnot
        unfold Ctx.tiltW at hwiPos
        simp [hnot] at hwiPos
      have hcut : 0 < D.cut := by exact Real.exp_pos _
      have hminusPos : 0 < D.dMinus Θ g i := lt_of_lt_of_le hcut hopen.1
      have hplusLower : (3 / 4 : ℝ) * D.dMinus Θ g i ≤ D.dPlus Θ g i := by
        calc
          (3 / 4 : ℝ) * D.dMinus Θ g i ≤ (1 - D.Δ) * D.dMinus Θ g i :=
            mul_le_mul_of_nonneg_right hDeltaLow hminus
          _ ≤ D.dPlus Θ g i := hopen.2
      have hplusPos : 0 < D.dPlus Θ g i :=
        lt_of_lt_of_le (mul_pos (by norm_num) hminusPos) hplusLower
      have hsumIte : (∑ y, if D.ownHit Θ g y then (D.M.μ i).w y else 0) =
          D.dPlus Θ g i := by
        unfold Ctx.dPlus
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : D.ownHit Θ g y <;> simp [hy]
      have htotalPosIte : 0 < ∑ y,
          if D.ownHit Θ g y then (D.M.μ i).w y else 0 := by
        simpa [hsumIte] using hplusPos
      have hUformula : (D.anchorU Θ g i).w x =
          ((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) / D.dPlus Θ g i := by
        unfold Ctx.anchorU
        change (if (∑ y, (D.M.μ i).w y * (if D.ownHit Θ g y then 1 else 0)) = 0 then
          (D.M.μ i).w x else
          ((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) /
          (∑ y, (D.M.μ i).w y * (if D.ownHit Θ g y then 1 else 0))) = _
        simp [Ctx.dPlus, ne_of_gt htotalPosIte]
      have hUbound : (D.anchorU Θ g i).w x ≤
          ((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) /
            ((3 / 4 : ℝ) * D.dMinus Θ g i) := by
        rw [hUformula]
        apply div_le_div_of_nonneg_left
        · exact mul_nonneg ((D.M.μ i).nonneg x) (ind_nonneg _)
        · exact mul_pos (by norm_num) hminusPos
        · exact hplusLower
      have htiltBound : (D.tilt Θ g).w i ≤
          (D.postW (Θ g) i * D.dMinus Θ g i) / ((4 / 5 : ℝ) * D.AG g) := by
        rw [htiltLaw]
        have hnum : D.tiltW Θ g i ≤ D.postW (Θ g) i * D.dMinus Θ g i := by
          unfold Ctx.tiltW
          split_ifs with hg <;> simp [hpost, hminus]
        have hnum' := mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hZ.le)
        have hden' := mul_le_mul_of_nonneg_left hInvZ
          (mul_nonneg hpost hminus)
        calc
          D.tiltW Θ g i * (D.ZG Θ g)⁻¹ ≤
              (D.postW (Θ g) i * D.dMinus Θ g i) * (D.ZG Θ g)⁻¹ := hnum'
          _ ≤ (D.postW (Θ g) i * D.dMinus Θ g i) * ((4 / 5 : ℝ) * D.AG g)⁻¹ := hden'
          _ = _ := by simp only [div_eq_mul_inv]
      have hterm0 := mul_le_mul_of_nonneg_right htiltBound
        (mul_nonneg (by positivity : 0 ≤ (D.N : ℝ)) ((D.anchorU Θ g i).nonneg x))
      have hterm1 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hUbound (by positivity : 0 ≤ (D.N : ℝ)))
        (by positivity : 0 ≤ (D.postW (Θ g) i * D.dMinus Θ g i) /
          ((4 / 5 : ℝ) * D.AG g))
      have hterm : (D.tilt Θ g).w i * ((D.N : ℝ) * (D.anchorU Θ g i).w x) ≤
          ((D.postW (Θ g) i * D.dMinus Θ g i) / ((4 / 5 : ℝ) * D.AG g)) *
            ((D.N : ℝ) * (((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) /
              ((3 / 4 : ℝ) * D.dMinus Θ g i))) := hterm0.trans hterm1
      have hcancel :
          ((D.postW (Θ g) i * D.dMinus Θ g i) / ((4 / 5 : ℝ) * D.AG g)) *
            ((D.N : ℝ) * (((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) /
              ((3 / 4 : ℝ) * D.dMinus Θ g i))) =
          (5 / (3 * D.AG g)) *
            (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) *
              (if D.ownHit Θ g x then 1 else 0) := by
        field_simp [ne_of_gt hAG, ne_of_gt hminusPos]
      rw [hcancel] at hterm
      have hhit : (if D.ownHit Θ g x then (1 : ℝ) else 0) ≤
          if D.crossHit Θ g x then 1 else 0 := by
        by_cases hx : D.ownHit Θ g x
        · have hcross : D.crossHit Θ g x := hx.1
          simp [hx, hcross]
        · simpa [hx] using ind_nonneg (D.crossHit Θ g x)
      have hcoef : 0 ≤ (5 / (3 * D.AG g)) *
          (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by
        apply mul_nonneg
        · exact div_nonneg (by norm_num) (by positivity)
        · exact mul_nonneg hpost (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
      exact hterm.trans (mul_le_mul_of_nonneg_left hhit hcoef)
  have hsum : (∑ i, (D.tilt Θ g).w i * ((D.N : ℝ) * (D.anchorU Θ g i).w x)) ≤
      (5 / (3 * D.AG g)) * (if D.crossHit Θ g x then 1 else 0) *
        ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
    calc
      _ ≤ ∑ i, (5 / (3 * D.AG g)) *
          (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) *
            (if D.crossHit Θ g x then 1 else 0) :=
        Finset.sum_le_sum fun i _ => hCrossTerm i
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hsumNonneg : 0 ≤ ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (D.postW_nonneg _ _) (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
  have hratio : 5 / (3 * D.AG g) ≤ 2 * (D.AG g)⁻¹ := by
    have hden : 0 < 3 * D.AG g := by positivity
    rw [div_le_iff₀ hden]
    field_simp [ne_of_gt hAG]
    norm_num
  have hB : D.Bcomp Θ g x =
      8 * (D.AG g)⁻¹ * (if D.crossHit Θ g x then 1 else 0) *
        ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
    simp [Ctx.Bcomp, hbase]
  have hbound : (D.tilt Θ g).expect (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x) ≤
      (8 * (D.AG g)⁻¹ * (if D.crossHit Θ g x then 1 else 0) *
        ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) / 4 := by
    have hfactor : 0 ≤ (if D.crossHit Θ g x then 1 else 0) *
        ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) :=
      by
        by_cases hx : D.crossHit Θ g x <;> simp [hx, hsumNonneg]
    unfold FinProb.expect
    calc
      (∑ i, (D.tilt Θ g).w i * ((D.N : ℝ) * (D.anchorU Θ g i).w x)) ≤
          (5 / (3 * D.AG g)) * (if D.crossHit Θ g x then 1 else 0) *
            ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := hsum
      _ ≤ 2 * (D.AG g)⁻¹ * (if D.crossHit Θ g x then 1 else 0) *
            ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x) := by
          calc
            _ = (5 / (3 * D.AG g)) *
                ((if D.crossHit Θ g x then 1 else 0) *
                  ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by ring
            _ ≤ (2 * (D.AG g)⁻¹) *
                ((if D.crossHit Θ g x then 1 else 0) *
                  ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) :=
              mul_le_mul_of_nonneg_right hratio hfactor
            _ = _ := by ring
      _ = _ := by ring
  calc
    (D.tilt Θ g).expect (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x) ≤
        (8 * (D.AG g)⁻¹ * (if D.crossHit Θ g x then 1 else 0) *
          ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) / 4 := hbound
    _ = D.Bcomp Θ g x / 4 := by rw [hB]

private theorem tag_anchor_expect {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (Θ : D.Hist) (g : D.KeyT) (ℓ : D.Loc) (x : Fin D.N) :
    (D.tagLawAll Θ).expect (fun t => (D.N : ℝ) * (D.anchorU Θ g (t g ℓ)).w x) =
      (D.tilt Θ g).expect (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x) := by
  classical
  calc
    (D.tagLawAll Θ).expect (fun t => (D.N : ℝ) * (D.anchorU Θ g (t g ℓ)).w x) =
        (FinProb.pi (fun _ : D.Loc => D.tilt Θ g)).expect
          (fun t => (D.N : ℝ) * (D.anchorU Θ g (t ℓ)).w x) := by
      exact pi_singleton_expect
        (fun k : D.KeyT => FinProb.pi (fun _ : D.Loc => D.tilt Θ k))
        g (fun t => (D.N : ℝ) * (D.anchorU Θ g (t ℓ)).w x)
    _ = (D.tilt Θ g).expect (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x) := by
      exact pi_singleton_expect (fun _ : D.Loc => D.tilt Θ g) ℓ
        (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x)

private theorem lane_scaleIndex_exists (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  have hM0 : M ≠ 0 := by omega
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      let z := M ^ i * R
      have hz0 : z ≠ 0 := by
        dsimp [z]
        exact Nat.mul_ne_zero (pow_ne_zero _ hM0) (by omega)
      have hz : 1 ≤ z := by omega
      have hstep : z + 1 ≤ 2 * z := by omega
      have hmult : 2 * z ≤ M * z := Nat.mul_le_mul_right z hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ z + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * z := hstep
        _ ≤ M * z := hmult
        _ = M ^ (i + 1) * R := by dsimp [z]; rw [pow_succ]; ring

private theorem topScale_sq_bound (σ ζ : ℝ) (hσ : 0 < σ) (hσζ : σ < ζ) (hζ : ζ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, topScale n σ ζ ≤ 8 * n ^ 2 := by
  have hσ1 : σ < 1 := lt_trans hσζ hζ
  refine ⟨1, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hM : 2 ≤ M := by dsimp [M]; omega
  have hR : 1 ≤ R₀ := by dsimp [R₀]; omega
  let hexists := lane_scaleIndex_exists M R₀ target hM hR
  let i : ℕ := Nat.find hexists
  have htop : topScale n σ ζ = M ^ i * R₀ := by
    dsimp [topScale, M, R₀, target, i, hexists]
  have hRlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogle : Real.log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos hnpos
    linarith
  have hlogsq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hceilR : (Nat.ceil (Real.log (n : ℝ) ^ 2) : ℝ) ≤
      (Real.log (n : ℝ)) ^ 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ Real.log (n : ℝ) ^ 2)).le
  have hRcast : (R₀ : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    dsimp [R₀]
    rw [Nat.cast_max]
    apply max_le_iff.mpr
    constructor
    · have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hnR 2)
      have htwo : (2 : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
        simpa [mul_one] using
          (mul_le_mul_of_nonneg_left hn2 (by norm_num : 0 ≤ (2 : ℝ)))
      have hOne : (1 : ℝ) ≤ 2 := by norm_num
      exact_mod_cast (le_trans hOne htwo)
    · calc
        (Nat.ceil (Real.log (n : ℝ) ^ 2) : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 + 1 := hceilR
        _ ≤ (n : ℝ) ^ 2 + 1 := by simpa [add_comm] using add_le_add_right hlogsq 1
        _ ≤ 2 * (n : ℝ) ^ 2 := by nlinarith [hnR]
  have hRnat : R₀ ≤ 2 * n ^ 2 := by exact_mod_cast hRcast
  have hσpow : (n : ℝ) ^ σ ≤ n := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR hσ1.le
    simpa [Real.rpow_one] using h
  have hceilM : (Nat.ceil ((n : ℝ) ^ σ) : ℝ) ≤ (n : ℝ) ^ σ + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hMcast : (M : ℝ) ≤ 3 * (n : ℝ) := by
    dsimp [M]
    rw [Nat.cast_max]
    apply max_le_iff.mpr
    constructor
    · calc
        (2 : ℝ) ≤ 3 := by norm_num
        _ = 3 * 1 := by ring
        _ ≤ 3 * (n : ℝ) := mul_le_mul_of_nonneg_left hnR (by norm_num)
    · calc
        (Nat.ceil ((n : ℝ) ^ σ) : ℝ) ≤ (n : ℝ) ^ σ + 1 := hceilM
        _ ≤ (n : ℝ) + 1 := by simpa [add_comm] using add_le_add_right hσpow 1
        _ ≤ 3 * (n : ℝ) := by nlinarith [hnR]
  have hexp : 1 - ζ ≤ 1 := by linarith [hσ, hσζ]
  have htargetPow : (n : ℝ) ^ (1 - ζ) ≤ n := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR hexp
    simpa [Real.rpow_one] using h
  have hceilT : (Nat.ceil ((n : ℝ) ^ (1 - ζ)) : ℝ) ≤
      (n : ℝ) ^ (1 - ζ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have htargetCast : (target : ℝ) ≤ 2 * (n : ℝ) := by
    dsimp [target]
    calc
      (Nat.ceil ((n : ℝ) ^ (1 - ζ)) : ℝ) ≤ (n : ℝ) ^ (1 - ζ) + 1 := hceilT
      _ ≤ (n : ℝ) + 1 := by simpa [add_comm] using add_le_add_right htargetPow 1
      _ ≤ 2 * (n : ℝ) := by nlinarith [hnR]
  have hprodCast : (M : ℝ) * target ≤ 6 * (n : ℝ) ^ 2 := by
    have hmul := mul_le_mul hMcast htargetCast (by positivity : 0 ≤ (target : ℝ))
      (by positivity : 0 ≤ 3 * (n : ℝ))
    nlinarith
  have hprodNat : M * target ≤ 8 * n ^ 2 := by
    have hcast : (M * target : ℝ) ≤ 8 * (n : ℝ) ^ 2 := by exact hprodCast.trans (by nlinarith)
    exact_mod_cast hcast
  have hiSpec : target ≤ M ^ i * R₀ := Nat.find_spec hexists
  by_cases hi0 : i = 0
  · rw [htop, hi0]
    simpa using hRnat.trans (by omega : 2 * n ^ 2 ≤ 8 * n ^ 2)
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    let j : ℕ := i - 1
    have hjlt : j < i := by dsimp [j]; omega
    have hprevNot : ¬ target ≤ M ^ j * R₀ := Nat.find_min hexists hjlt
    have hprev : M ^ j * R₀ < target := by omega
    have hpow : M ^ i * R₀ = M * (M ^ j * R₀) := by
      have hEq : i = j + 1 := by dsimp [j]; omega
      rw [hEq, pow_succ]
      ring
    have hupper : M ^ i * R₀ ≤ M * target := by
      rw [hpow]
      exact Nat.mul_le_mul_left M hprev.le
    rw [htop]
    exact hupper.trans hprodNat

private theorem exp_poly_small (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (n : ℝ) ^ k * Real.exp (-(n : ℝ) ^ c) ≤ 1 / 64 := by
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  have hpoly : Tendsto
      (fun n : ℕ => ((n : ℝ) ^ c) ^ ((k : ℝ) / c) * Real.exp (-(n : ℝ) ^ c))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((k : ℝ) / c) 1 one_pos).comp htend
    simpa [Function.comp_def] using h
  have hev : ∀ᶠ n : ℕ in atTop,
      ((n : ℝ) ^ c) ^ ((k : ℝ) / c) * Real.exp (-(n : ℝ) ^ c) < 1 / 64 :=
    hpoly.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpow : ((n : ℝ) ^ c) ^ ((k : ℝ) / c) = (n : ℝ) ^ k := by
    rw [← Real.rpow_mul hnpos.le]
    have he : c * ((k : ℝ) / c) = (k : ℝ) := by field_simp [ne_of_gt hc]
    rw [he, ← Real.rpow_natCast]
  have hsmall := hn₀ n hn0
  simpa [hpow] using hsmall.le

private theorem expect_const {α : Type*} [Fintype α] (P : FinProb α) (c : ℝ) :
    P.expect (fun _ => c) = c := by
  unfold FinProb.expect
  calc
    (∑ a, P.w a * c) = (∑ a, P.w a) * c := by rw [Finset.sum_mul]
    _ = c := by rw [P.sum_eq_one]; ring

private theorem expect_sum {α ι : Type*} [Fintype α] [Fintype ι]
    (P : FinProb α) (f : α → ι → ℝ) :
    P.expect (fun a => ∑ i, f a i) = ∑ i, P.expect (fun a => f a i) := by
  classical
  unfold FinProb.expect
  change (∑ a, P.w a * ∑ i, f a i) = ∑ i, ∑ a, P.w a * f a i
  calc
    (∑ a, P.w a * ∑ i, f a i) = ∑ a, ∑ i, P.w a * f a i := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ i, ∑ a, P.w a * f a i := Finset.sum_comm

private theorem prod_pr_integral {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (E : α → β → Prop) :
    (FinProb.prod P Q).pr (fun z => E z.1 z.2) =
      P.expect (fun a => Q.pr (E a)) := by
  classical
  calc
    (FinProb.prod P Q).pr (fun z => E z.1 z.2) =
        (FinProb.prod P Q).expect (fun z => if E z.1 z.2 then 1 else 0) := by
          simpa using (FinProb.pr_indicator (FinProb.prod P Q) (fun z => E z.1 z.2))
    _ = P.expect (fun a => Q.expect (fun b => if E a b then 1 else 0)) :=
          prod_expect P Q (fun a b => if E a b then 1 else 0)
    _ = P.expect (fun a => Q.pr (E a)) := by
          apply expect_congr
          intro a
          simpa using (FinProb.pr_indicator Q (E a)).symm

private theorem prod_pr_ignore_right {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (E : α → Prop) :
    (FinProb.prod P Q).pr (fun z => E z.1) = P.pr E := by
  classical
  rw [prod_pr_integral P Q (fun a _ => E a)]
  calc
    P.expect (fun a => Q.pr (fun _ => E a)) =
        P.expect (fun a => if E a then 1 else 0) := by
          apply expect_congr
          intro a
          by_cases h : E a
          · simp [h, FinProb.pr, Q.sum_eq_one]
          · simp [h, FinProb.pr]
    _ = P.pr E := by simpa using (FinProb.pr_indicator P E).symm

private theorem prod_pr_ignore_left {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (E : β → Prop) :
    (FinProb.prod P Q).pr (fun z => E z.2) = Q.pr E := by
  rw [prod_pr_integral P Q (fun _ b => E b), expect_const]

private theorem tagLawAll_positive_support {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) :
    (D.tagLawAll Θ).pr (fun t => ∀ g ℓ, 0 < (D.tilt Θ g).w (t g ℓ)) = 1 := by
  classical
  have hloc (g : D.KeyT) :
      (FinProb.pi (fun _ : D.Loc => D.tilt Θ g)).pr
        (fun t => ∀ ℓ, 0 < (D.tilt Θ g).w (t ℓ)) = 1 := by
    simpa [pr_positive_weight_eq_one] using
      (pi_pr_forall (ι := D.Loc) (Ω := fun _ : D.Loc => D.M.ι)
        (P := fun _ : D.Loc => D.tilt Θ g) (Finset.univ : Finset D.Loc)
        (fun _ ℓ => 0 < (D.tilt Θ g).w ℓ))
  have hpi0 := pi_pr_forall (ι := D.KeyT) (Ω := fun _ : D.KeyT => D.Loc → D.M.ι)
      (P := fun g => FinProb.pi (fun _ : D.Loc => D.tilt Θ g))
      (Finset.univ : Finset D.KeyT) (fun g t => ∀ ℓ, 0 < (D.tilt Θ g).w (t ℓ))
  have houter : (D.tagLawAll Θ).pr
      (fun t => ∀ g ℓ, 0 < (D.tilt Θ g).w (t g ℓ)) =
      ∏ g ∈ Finset.univ,
        (FinProb.pi (fun _ : D.Loc => D.tilt Θ g)).pr
          (fun t => ∀ ℓ, 0 < (D.tilt Θ g).w (t ℓ)) := by
    simpa [Ctx.tagLawAll] using hpi0
  rw [houter]
  calc
    (∏ g ∈ Finset.univ,
        (FinProb.pi (fun _ : D.Loc => D.tilt Θ g)).pr
          (fun t => ∀ ℓ, 0 < (D.tilt Θ g).w (t ℓ))) =
      ∏ g ∈ Finset.univ, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro g hg
        exact hloc g
    _ = 1 := by simp

set_option maxHeartbeats 5000000 in
private theorem rawTAT_tagSupport_pr_one {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) :
    (D.rawTAT Θ).pr (fun ω => ∀ g ℓ, 0 < (D.tilt Θ g).w (ω.1.1 g ℓ)) = 1 := by
  calc
    (D.rawTAT Θ).pr (fun ω => ∀ g ℓ, 0 < (D.tilt Θ g).w (ω.1.1 g ℓ)) =
      (((D.tagLawAll Θ).prod D.actLaw).prod D.tieLaw).pr
        (fun z => ∀ g ℓ, 0 < (D.tilt Θ g).w (z.1.1 g ℓ)) := by
          rfl
    _ = ((D.tagLawAll Θ).prod D.actLaw).pr
        (fun z => ∀ g ℓ, 0 < (D.tilt Θ g).w (z.1 g ℓ)) :=
          prod_pr_ignore_right ((D.tagLawAll Θ).prod D.actLaw) D.tieLaw
            (fun z : D.Tags × D.Acts => ∀ g ℓ, 0 < (D.tilt Θ g).w (z.1 g ℓ))
    _ = (D.tagLawAll Θ).pr (fun t => ∀ g ℓ, 0 < (D.tilt Θ g).w (t g ℓ)) := by
          exact prod_pr_ignore_right (D.tagLawAll Θ) D.actLaw
            (fun t => ∀ g ℓ, 0 < (D.tilt Θ g).w (t g ℓ))
    _ = 1 := tagLawAll_positive_support D Θ

set_option maxHeartbeats 5000000 in
private theorem posTAT_tagSupport_pr_one {η₀ β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (Θ : D.Hist) :
    (FinProb.prod D.posLaw (D.rawTAT Θ)).pr
    (fun z => ∀ g ℓ, 0 < (D.tilt Θ g).w (z.2.1.1 g ℓ)) = 1 := by
  calc
    (FinProb.prod D.posLaw (D.rawTAT Θ)).pr
        (fun z => ∀ g ℓ, 0 < (D.tilt Θ g).w (z.2.1.1 g ℓ)) =
      (D.rawTAT Θ).pr (fun ω => ∀ g ℓ, 0 < (D.tilt Θ g).w (ω.1.1 g ℓ)) :=
        prod_pr_ignore_left D.posLaw (D.rawTAT Θ)
          (fun ω => ∀ g ℓ, 0 < (D.tilt Θ g).w (ω.1.1 g ℓ))
    _ = 1 := rawTAT_tagSupport_pr_one D Θ

private noncomputable def centerAnchorCap (η₀ γ : ℝ) {β p : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) : ℝ :=
  Real.exp ((D.n : ℝ) ^ γ + Real.log 2 + (D.n : ℝ) ^ (2 * tau8 η₀)) / (1 - D.Δ)

private theorem inv_one_sub_exp_neg_le {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by
  have hExp : 1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
  have hInvExp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) (by positivity)).mpr hExp
  have hLower : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    have hEq : 1 - (1 + x)⁻¹ = x / (1 + x) := by field_simp; ring
    rw [← hEq]
    exact sub_le_sub_left hInvExp 1
  have hDen : 0 < 1 - Real.exp (-x) := by
    have hlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
    linarith
  calc
    (1 - Real.exp (-x))⁻¹ ≤ (x / (1 + x))⁻¹ :=
      (inv_le_inv₀ hDen (div_pos hx (by positivity))).mpr hLower
    _ = 1 + x⁻¹ := by field_simp [ne_of_gt hx]; ring

private theorem centerAnchorCap_small (η₀ γ p c : ℝ)
    (hη₀ : 0 < η₀) (hγ₁ : γ < 1) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      (n : ℝ) * Real.exp (-c * n) *
        (Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) /
          (1 - Real.exp (-(n : ℝ) ^ (p / 2)))) ≤ 1 := by
  have hτ : 0 < tau8 η₀ := tau8_pos hη₀
  have h2τ : 2 * tau8 η₀ < 1 := by
    rw [tau8_eq]
    have hη8 : eta8 η₀ ≤ 4 / 100 := min_le_right _ _
    nlinarith
  let r : ℝ := max (max γ (2 * tau8 η₀)) (1 / 2)
  have hr0 : 0 < r := by dsimp [r]; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr1 : r < 1 := by
    dsimp [r]
    exact max_lt (max_lt hγ₁ h2τ) (by norm_num)
  let k : ℕ := Nat.ceil (max 0 (-p / 2))
  have hk : -p / 2 ≤ (k : ℝ) := by
    dsimp [k]
    exact le_trans (le_max_right _ _) (Nat.le_ceil _)
  obtain ⟨nPoly, hPoly⟩ := exp_poly_small r hr0 k
  have hRatio : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 - r))) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < (1 - r))).comp
      tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using h
  have hRatioSmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 - r)) < c / 20 :=
    hRatio.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨nRatio, hnRatio⟩ := Filter.eventually_atTop.1 hRatioSmall
  have hPower : Tendsto (fun n : ℕ => (n : ℝ) ^ r) atTop atTop :=
    (tendsto_rpow_atTop hr0).comp tendsto_natCast_atTop_atTop
  have hPowerLarge : ∀ᶠ n : ℕ in atTop, Real.log 4 ≤ (n : ℝ) ^ r :=
    hPower.eventually (eventually_ge_atTop (Real.log 4))
  obtain ⟨nFour, hnFour⟩ := Filter.eventually_atTop.1 hPowerLarge
  let a : ℝ := c / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hLinear : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop ha
  have hDecay : Tendsto
      (fun n : ℕ => (a * (n : ℝ)) ^ (1 : ℝ) * Real.exp (-(a * (n : ℝ))))
      atTop (nhds 0) := by
    simpa [Function.comp_def, Real.rpow_one, neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos).comp hLinear
  have hDecaySmall : ∀ᶠ n : ℕ in atTop,
      (a * (n : ℝ)) ^ (1 : ℝ) * Real.exp (-(a * (n : ℝ))) < a / 4 :=
    hDecay.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨nLin, hnLin⟩ := Filter.eventually_atTop.1 hDecaySmall
  let n₀ := max 1 (max nPoly (max nRatio (max nFour nLin)))
  refine ⟨n₀, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by dsimp [n₀] at hn; omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hnPoly : nPoly ≤ n := by dsimp [n₀] at hn; omega
  have hnRatio0 : nRatio ≤ n := by dsimp [n₀] at hn; omega
  have hnFour0 : nFour ≤ n := by dsimp [n₀] at hn; omega
  have hnLin0 : nLin ≤ n := by dsimp [n₀] at hn; omega
  have hrγ : γ ≤ r := by dsimp [r]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hrτ : 2 * tau8 η₀ ≤ r := by dsimp [r]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hγpow : (n : ℝ) ^ γ ≤ (n : ℝ) ^ r := Real.rpow_le_rpow_of_exponent_le hnR hrγ
  have hτpow : (n : ℝ) ^ (2 * tau8 η₀) ≤ (n : ℝ) ^ r := Real.rpow_le_rpow_of_exponent_le hnR hrτ
  have hxpos : 0 < (n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnpos _
  have hpowNeg : (n : ℝ) ^ (-p / 2) = ((n : ℝ) ^ (p / 2))⁻¹ := by
    have h := Real.rpow_neg (le_of_lt hnpos) (p / 2)
    convert h using 1 <;> congr 1 <;> ring
  have hinvDelta : (1 - Real.exp (-(n : ℝ) ^ (p / 2)))⁻¹ ≤ 1 + (n : ℝ) ^ (-p / 2) := by
    simpa [hpowNeg] using inv_one_sub_exp_neg_le hxpos
  have hnegativePow : (n : ℝ) ^ (-p / 2) ≤ (n : ℝ) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR hk
  have hpolyNow : (n : ℝ) ^ k * Real.exp (-(n : ℝ) ^ r) ≤ 1 / 64 := hPoly n hnPoly
  have hExpBase :
      Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) ≤
        2 * Real.exp (2 * (n : ℝ) ^ r) := by
    have hlog2 : Real.log 2 ≤ (n : ℝ) ^ r := by
      calc
        Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
        _ ≤ (n : ℝ) ^ r := hnFour n hnFour0
    calc
      Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) ≤
          Real.exp (Real.log 2 + 2 * (n : ℝ) ^ r) :=
        Real.exp_le_exp.mpr (by nlinarith [hγpow, hτpow, hlog2])
      _ = 2 * Real.exp (2 * (n : ℝ) ^ r) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hcap :
      Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) /
        (1 - Real.exp (-(n : ℝ) ^ (p / 2))) ≤ 4 * Real.exp (4 * (n : ℝ) ^ r) := by
    have hpolyExp : (n : ℝ) ^ (k : ℝ) ≤ Real.exp ((n : ℝ) ^ r) := by
      have hpowEq : (n : ℝ) ^ (k : ℝ) = (n : ℝ) ^ k := Real.rpow_natCast (n : ℝ) k
      have hRpowPos : 0 < Real.exp (-(n : ℝ) ^ r) := Real.exp_pos _
      have hmul := (le_div_iff₀ hRpowPos).2 hpolyNow
      have hdiv : (1 / 64 : ℝ) / Real.exp (-(n : ℝ) ^ r) ≤ Real.exp ((n : ℝ) ^ r) := by
        rw [Real.exp_neg]
        have heq : (1 / 64 : ℝ) / (Real.exp ((n : ℝ) ^ r))⁻¹ =
            (1 / 64 : ℝ) * Real.exp ((n : ℝ) ^ r) := by
          field_simp
        rw [heq]
        calc
          (1 / 64 : ℝ) * Real.exp ((n : ℝ) ^ r) ≤
              1 * Real.exp ((n : ℝ) ^ r) := by gcongr <;> norm_num
          _ = Real.exp ((n : ℝ) ^ r) := by ring
      calc
        (n : ℝ) ^ (k : ℝ) = (n : ℝ) ^ k := hpowEq
        _ ≤ (1 / 64 : ℝ) / Real.exp (-(n : ℝ) ^ r) := hmul
        _ ≤ Real.exp ((n : ℝ) ^ r) := hdiv
    have hfactor : (1 - Real.exp (-(n : ℝ) ^ (p / 2)))⁻¹ ≤
        2 * Real.exp ((n : ℝ) ^ r) := by
      have hle : (n : ℝ) ^ (-p / 2) ≤ (n : ℝ) ^ (k : ℝ) := hnegativePow
      have hone : (1 : ℝ) ≤ Real.exp ((n : ℝ) ^ r) := Real.one_le_exp (by positivity)
      calc
        (1 - Real.exp (-(n : ℝ) ^ (p / 2)))⁻¹ ≤ 1 + (n : ℝ) ^ (-p / 2) := hinvDelta
        _ ≤ 2 * Real.exp ((n : ℝ) ^ r) := by nlinarith [hpolyExp]
    calc
      _ = Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) *
          (1 - Real.exp (-(n : ℝ) ^ (p / 2)))⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) *
          (2 * Real.exp ((n : ℝ) ^ r)) := by
            exact mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
      _ ≤ (2 * Real.exp (2 * (n : ℝ) ^ r)) * (2 * Real.exp ((n : ℝ) ^ r)) :=
            mul_le_mul_of_nonneg_right hExpBase (by positivity)
      _ = 4 * Real.exp (3 * (n : ℝ) ^ r) := by
            calc
              _ = 4 * (Real.exp (2 * (n : ℝ) ^ r) * Real.exp ((n : ℝ) ^ r)) := by ring
              _ = 4 * Real.exp (3 * (n : ℝ) ^ r) := by
                rw [← Real.exp_add]
                congr 1
                ring
      _ ≤ 4 * Real.exp (4 * (n : ℝ) ^ r) := by
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by
                have hq : 0 ≤ (n : ℝ) ^ r := (Real.rpow_pos_of_pos hnpos r).le
                nlinarith)) (by norm_num)
  have hfourExp : 4 ≤ Real.exp ((n : ℝ) ^ r) := by
    calc
      (4 : ℝ) = Real.exp (Real.log 4) := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ Real.exp ((n : ℝ) ^ r) := Real.exp_le_exp.mpr (hnFour n hnFour0)
  have hratioNow : (n : ℝ) ^ (-(1 - r)) < c / 20 := hnRatio n hnRatio0
  have hpowRatio : (n : ℝ) ^ r = (n : ℝ) * (n : ℝ) ^ (-(1 - r)) := by
    calc
      (n : ℝ) ^ r = (n : ℝ) ^ (1 + -(1 - r)) := by congr 1 <;> ring
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 - r)) := by rw [Real.rpow_add hnpos]
      _ = (n : ℝ) * (n : ℝ) ^ (-(1 - r)) := by simp [Real.rpow_one]
  have hsublinear : 5 * (n : ℝ) ^ r ≤ (c / 2) * (n : ℝ) := by
    rw [hpowRatio]
    nlinarith [hratioNow, hnR]
  have hcapLinear :
      Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) /
        (1 - Real.exp (-(n : ℝ) ^ (p / 2))) ≤ Real.exp (a * (n : ℝ)) := by
    calc
      _ ≤ 4 * Real.exp (4 * (n : ℝ) ^ r) := hcap
      _ ≤ Real.exp (5 * (n : ℝ) ^ r) := by
        calc
          4 * Real.exp (4 * (n : ℝ) ^ r) =
              Real.exp (Real.log 4) * Real.exp (4 * (n : ℝ) ^ r) := by
                rw [Real.exp_log (by norm_num : (0 : ℝ) < 4)]
          _ = Real.exp (Real.log 4 + 4 * (n : ℝ) ^ r) := by rw [Real.exp_add]
          _ ≤ Real.exp (5 * (n : ℝ) ^ r) := Real.exp_le_exp.mpr (by
                have := hnFour n hnFour0
                nlinarith)
      _ ≤ Real.exp (a * (n : ℝ)) := Real.exp_le_exp.mpr (by
        dsimp [a]
        linarith [hsublinear])
  have hdecayNow : (n : ℝ) * Real.exp (-(a * (n : ℝ))) ≤ 1 / 4 := by
    have hsmall := hnLin n hnLin0
    have hsmall' : a * (n : ℝ) * Real.exp (-(a * (n : ℝ))) < a / 4 := by
      simpa [Real.rpow_one] using hsmall
    have hdiv : (n : ℝ) * Real.exp (-(a * (n : ℝ))) < 1 / 4 := by
      calc
        (n : ℝ) * Real.exp (-(a * (n : ℝ))) =
            (a * (n : ℝ) * Real.exp (-(a * (n : ℝ)))) / a := by
          field_simp [ne_of_gt ha]
        _ < (a / 4) / a := div_lt_div_of_pos_right hsmall' ha
        _ = 1 / 4 := by field_simp [ne_of_gt ha]
    exact hdiv.le
  have hExpCombine : Real.exp (-c * (n : ℝ)) * Real.exp (a * (n : ℝ)) =
      Real.exp (-(a * (n : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [a]
    ring
  calc
    (n : ℝ) * Real.exp (-c * (n : ℝ)) *
        (Real.exp ((n : ℝ) ^ γ + Real.log 2 + (n : ℝ) ^ (2 * tau8 η₀)) /
          (1 - Real.exp (-(n : ℝ) ^ (p / 2)))) ≤
      (n : ℝ) * Real.exp (-c * (n : ℝ)) * Real.exp (a * (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcapLinear (by positivity)
    _ = (n : ℝ) * Real.exp (-(a * (n : ℝ))) := by
      calc
        _ = (n : ℝ) * (Real.exp (-c * (n : ℝ)) * Real.exp (a * (n : ℝ))) := by ring
        _ = _ := by rw [hExpCombine]
    _ ≤ 1 := by linarith [hdecayNow]

private theorem anchorU_cap_of_tag_support {η₀ γ β p K : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (X Y R : Finset (Fin D.N)) (hStd : Std D γ K X Y R)
    (Θ : D.Hist) (hgood : ∀ g, ¬ D.HBad Θ g) (hn : 0 < D.n)
    (e : D.CellT) (x : Fin D.N)
    (i : D.M.ι) (hTag : 0 < (D.tilt Θ e.1).w i) :
    (D.N : ℝ) * (D.anchorU Θ e.1 i).w x ≤ centerAnchorCap η₀ γ D := by
  classical
  let g : D.KeyT := e.1
  have hbase : D.BaseGates Θ g := by
    by_contra hnot
    exact hgood g (by simp [Ctx.HBad, hnot])
  have hAG : 0 < D.AG g := by unfold Ctx.AG; positivity
  have hZ : 0 < D.ZG Θ g := by
    have hlow := hbase.2.1.1
    exact lt_of_lt_of_le (mul_pos (by norm_num) hAG) hlow
  have htiltFormula : (D.tilt Θ g).w i = D.tiltW Θ g i / D.ZG Θ g := by
    unfold Ctx.tilt
    unfold normOr
    change (if (∑ j, D.tiltW Θ g j) = 0 then D.tagLaw.w i else
      D.tiltW Θ g i / (∑ j, D.tiltW Θ g j)) = _
    have hsum : (∑ j, D.tiltW Θ g j) = D.ZG Θ g := rfl
    rw [hsum]
    simp [ne_of_gt hZ]
  have htiltW : 0 < D.tiltW Θ g i := by
    by_contra hnot
    have hzero : D.tiltW Θ g i = 0 := by
      exact le_antisymm (le_of_not_gt hnot) (D.tiltW_nonneg Θ g i)
    rw [htiltFormula, hzero] at hTag
    norm_num at hTag
  have hopen : D.GateOpen Θ g i := by
    by_contra hnot
    unfold Ctx.tiltW at htiltW
    simp [hnot] at htiltW
  have hcut : 0 < D.cut := Real.exp_pos _
  have hminus : 0 < D.dMinus Θ g i := lt_of_lt_of_le hcut hopen.1
  have hpost : 0 < D.postW (Θ g) i := by
    by_contra hnot
    have hzero : D.postW (Θ g) i = 0 :=
      le_antisymm (le_of_not_gt hnot) (D.postW_nonneg _ _)
    have htiltZero : D.tiltW Θ g i = 0 := by
      unfold Ctx.tiltW
      simp [hzero, hopen]
    exact (ne_of_gt htiltW) htiltZero
  have hLambda : 0 < D.M.Λ i := by
    by_contra hnot
    have hzero : D.M.Λ i = 0 := le_antisymm (le_of_not_gt hnot) (D.M.Λ_nonneg i)
    have hpostZero : D.postW (Θ g) i = 0 := by
      unfold Ctx.postW
      by_cases hR : D.R'.w (Θ g) = 0 <;> simp [hR, hzero]
    exact (ne_of_gt hpost) hpostZero
  have hDelta : D.Δ < 1 := by
    have hnR : (0 : ℝ) < (D.n : ℝ) := by exact_mod_cast hn
    have hpw : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
    unfold Ctx.Δ
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpw)
  have hfactor : 0 < 1 - D.Δ := sub_pos.mpr hDelta
  have hPlusLower : (1 - D.Δ) * D.cut ≤ D.dPlus Θ g i := by
    calc
      (1 - D.Δ) * D.cut ≤ (1 - D.Δ) * D.dMinus Θ g i :=
        mul_le_mul_of_nonneg_left hopen.1 hfactor.le
      _ ≤ D.dPlus Θ g i := hopen.2
  have hPlus : 0 < D.dPlus Θ g i := lt_of_lt_of_le (mul_pos hfactor hminus) hopen.2
  rcases hStd.laws i hLambda with ⟨_, _, hwidth, _, _⟩
  have hNpos : 0 < (D.N : ℝ) := by exact_mod_cast hStd.size.1
  have hNμ : (D.N : ℝ) * (D.M.μ i).w x ≤ Real.exp ((D.n : ℝ) ^ γ + Real.log 2) := by
    calc
      (D.N : ℝ) * (D.M.μ i).w x ≤
          (D.N : ℝ) * (Real.exp ((D.n : ℝ) ^ γ + Real.log 2) / D.N) :=
            mul_le_mul_of_nonneg_left (hwidth x) hNpos.le
      _ = Real.exp ((D.n : ℝ) ^ γ + Real.log 2) := by
            field_simp [ne_of_gt hNpos]
  have hUformula : (D.anchorU Θ g i).w x =
      ((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) / D.dPlus Θ g i := by
    unfold Ctx.anchorU
    change (if (∑ y, (D.M.μ i).w y * (if D.ownHit Θ g y then 1 else 0)) = 0 then
        (D.M.μ i).w x else
        ((D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0)) /
          (∑ y, (D.M.μ i).w y * (if D.ownHit Θ g y then 1 else 0))) = _
    have hsumNorm : (∑ y, if D.ownHit Θ g y then (D.M.μ i).w y else 0) =
        D.dPlus Θ g i := by
      unfold Ctx.dPlus
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : D.ownHit Θ g y <;> simp [hy]
    have hsumProd : (∑ y, (D.M.μ i).w y * (if D.ownHit Θ g y then 1 else 0)) =
        D.dPlus Θ g i := by
      calc
        (∑ y, (D.M.μ i).w y * (if D.ownHit Θ g y then 1 else 0)) =
            ∑ y, if D.ownHit Θ g y then (D.M.μ i).w y else 0 := by
              apply Finset.sum_congr rfl
              intro y _
              by_cases hy : D.ownHit Θ g y <;> simp [hy]
        _ = D.dPlus Θ g i := hsumNorm
    rw [hsumProd]
    simp [ne_of_gt hPlus]
  have hnum : (D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0) ≤ (D.M.μ i).w x := by
    have hindicator : (if D.ownHit Θ g x then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    calc
      (D.M.μ i).w x * (if D.ownHit Θ g x then 1 else 0) ≤ (D.M.μ i).w x * 1 :=
        mul_le_mul_of_nonneg_left hindicator ((D.M.μ i).nonneg x)
      _ = (D.M.μ i).w x := by ring
  have hUbound : (D.anchorU Θ g i).w x ≤ (D.M.μ i).w x / D.dPlus Θ g i := by
    rw [hUformula]
    exact div_le_div_of_nonneg_right hnum hPlus.le
  have hdenPos : 0 < (1 - D.Δ) * D.cut := mul_pos hfactor hcut
  have hden : (1 - D.Δ) * D.cut ≤ D.dPlus Θ g i := hPlusLower
  have hinv : (D.dPlus Θ g i)⁻¹ ≤ ((1 - D.Δ) * D.cut)⁻¹ :=
    (inv_le_inv₀ hPlus hdenPos).mpr hden
  have hbound : (D.N : ℝ) * (D.anchorU Θ g i).w x ≤
      Real.exp ((D.n : ℝ) ^ γ + Real.log 2) / ((1 - D.Δ) * D.cut) := by
    calc
      (D.N : ℝ) * (D.anchorU Θ g i).w x ≤
          (D.N : ℝ) * ((D.M.μ i).w x / D.dPlus Θ g i) :=
            mul_le_mul_of_nonneg_left hUbound hNpos.le
      _ = ((D.N : ℝ) * (D.M.μ i).w x) * (D.dPlus Θ g i)⁻¹ := by ring
      _ ≤ Real.exp ((D.n : ℝ) ^ γ + Real.log 2) *
          ((1 - D.Δ) * D.cut)⁻¹ :=
            mul_le_mul hNμ hinv (by positivity) (by positivity)
      _ = Real.exp ((D.n : ℝ) ^ γ + Real.log 2) / ((1 - D.Δ) * D.cut) := by rw [div_eq_mul_inv]
  unfold centerAnchorCap
  have hcutEq : D.cut = Real.exp (-(D.n : ℝ) ^ (2 * tau8 η₀)) := rfl
  rw [hcutEq] at hbound
  have hdenRewrite :
      Real.exp ((D.n : ℝ) ^ γ + Real.log 2) /
        ((1 - D.Δ) * Real.exp (-(D.n : ℝ) ^ (2 * tau8 η₀))) =
      Real.exp ((D.n : ℝ) ^ γ + Real.log 2 + (D.n : ℝ) ^ (2 * tau8 η₀)) / (1 - D.Δ) := by
    calc
      Real.exp ((D.n : ℝ) ^ γ + Real.log 2) /
          ((1 - D.Δ) * Real.exp (-(D.n : ℝ) ^ (2 * tau8 η₀))) =
        Real.exp ((D.n : ℝ) ^ γ + Real.log 2) *
          ((1 - D.Δ)⁻¹ * (Real.exp (-(D.n : ℝ) ^ (2 * tau8 η₀)))⁻¹) := by
            rw [div_eq_mul_inv, mul_inv]
      _ = Real.exp ((D.n : ℝ) ^ γ + Real.log 2) *
          ((1 - D.Δ)⁻¹ * Real.exp ((D.n : ℝ) ^ (2 * tau8 η₀))) := by simp [Real.exp_neg]
      _ = (Real.exp ((D.n : ℝ) ^ γ + Real.log 2) *
            Real.exp ((D.n : ℝ) ^ (2 * tau8 η₀))) * (1 - D.Δ)⁻¹ := by ring
      _ = Real.exp ((D.n : ℝ) ^ γ + Real.log 2 + (D.n : ℝ) ^ (2 * tau8 η₀)) *
            (1 - D.Δ)⁻¹ := by
              exact congrArg (fun z : ℝ => z * (1 - D.Δ)⁻¹)
                (Real.exp_add ((D.n : ℝ) ^ γ + Real.log 2)
                  ((D.n : ℝ) ^ (2 * tau8 η₀))).symm
      _ = Real.exp ((D.n : ℝ) ^ γ + Real.log 2 + (D.n : ℝ) ^ (2 * tau8 η₀)) /
            (1 - D.Δ) := by rw [div_eq_mul_inv]
  calc
    (D.N : ℝ) * (D.anchorU Θ e.1 i).w x ≤
        Real.exp ((D.n : ℝ) ^ γ + Real.log 2) /
          ((1 - D.Δ) * Real.exp (-(D.n : ℝ) ^ (2 * tau8 η₀))) := hbound
    _ = centerAnchorCap η₀ γ D := by
          unfold centerAnchorCap
          exact hdenRewrite

private theorem expect_event_const {α : Type*} [Fintype α]
    (P : FinProb α) (E : α → Prop) (c : ℝ) :
    P.expect (fun a => if E a then c else 0) = c * P.pr E := by
  classical
  unfold FinProb.expect FinProb.pr
  calc
    (∑ a, P.w a * (if E a then c else 0)) =
        ∑ a, c * (if E a then P.w a else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : E a <;> simp [h] <;> ring
    _ = c * ∑ a, if E a then P.w a else 0 := by rw [Finset.mul_sum]

private theorem pr_congr_weights {α : Type*} [Fintype α]
    (P Q : FinProb α) (hw : ∀ a, P.w a = Q.w a) (E : α → Prop) :
    P.pr E = Q.pr E := by
  classical
  unfold FinProb.pr
  apply Finset.sum_congr rfl
  intro a _
  rw [hw]

private theorem prod_pr_assoc {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : FinProb α) (Q : FinProb β) (R : FinProb γ) (E : α → β → γ → Prop) :
    (FinProb.prod P (FinProb.prod Q R)).pr
        (fun z => E z.1 z.2.1 z.2.2) =
      (FinProb.prod (FinProb.prod P Q) R).pr
        (fun z => E z.1.1 z.1.2 z.2) := by
  calc
    (FinProb.prod P (FinProb.prod Q R)).pr
        (fun z => E z.1 z.2.1 z.2.2) =
      (FinProb.prod P (FinProb.prod Q R)).expect
        (fun z => if E z.1 z.2.1 z.2.2 then 1 else 0) := by
          simpa using (FinProb.pr_indicator (FinProb.prod P (FinProb.prod Q R))
            (fun z => E z.1 z.2.1 z.2.2))
    _ = (FinProb.prod (FinProb.prod P Q) R).expect
        (fun z => if E z.1.1 z.1.2 z.2 then 1 else 0) :=
          (prod_expect_assoc P Q R (fun a b c => if E a b c then 1 else 0)).symm
    _ = (FinProb.prod (FinProb.prod P Q) R).pr
        (fun z => E z.1.1 z.1.2 z.2) := by
          simpa using (FinProb.pr_indicator (FinProb.prod (FinProb.prod P Q) R)
            (fun z => E z.1.1 z.1.2 z.2)).symm

private theorem expect_le_const {α : Type*} [Fintype α] (P : FinProb α)
    (f : α → ℝ) (c : ℝ) (hf : ∀ a, f a ≤ c) : P.expect f ≤ c := by
  calc
    P.expect f ≤ P.expect (fun _ => c) := FinProb.expect_mono P hf
    _ = c := expect_const P c

private theorem weighted_product_expect_pr_bound {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : ℝ) (hmEq : P.expect w = m) (hm : 0 < m) (E : α → β → Prop)
    (b : ℝ)
    (hprob : (FinProb.prod (weightedLaw P w hw m hm hmEq) Q).pr
      (fun z => E z.1 z.2) ≤ b) :
    P.expect (fun a => w a * Q.pr (E a)) ≤ m * b := by
  have hEq := weightedLaw_expect P w hw m hm hmEq (fun a => Q.pr (E a))
  calc
    P.expect (fun a => w a * Q.pr (E a)) =
        m * (weightedLaw P w hw m hm hmEq).expect (fun a => Q.pr (E a)) := hEq
    _ = m * (FinProb.prod (weightedLaw P w hw m hm hmEq) Q).pr
          (fun z => E z.1 z.2) := by rw [prod_pr_integral]
    _ ≤ m * b := mul_le_mul_of_nonneg_left hprob hm.le

private theorem weighted_product_expect_pr_zero {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    (m : ℝ) (hmEq : P.expect w = m) (hm : m = 0) (E : α → β → Prop) :
    P.expect (fun a => w a * Q.pr (E a)) ≤ 0 := by
  have hpoint : ∀ a, w a * Q.pr (E a) ≤ w a := by
    intro a
    have hpr := pr_le_one Q (E a)
    calc
      w a * Q.pr (E a) ≤ w a * 1 := mul_le_mul_of_nonneg_left hpr (hw a)
      _ = w a := by ring
  calc
    P.expect (fun a => w a * Q.pr (E a)) ≤ P.expect w := FinProb.expect_mono P hpoint
    _ = 0 := by rw [hmEq, hm]

private theorem weightedLaw_prod_right {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (w : β → ℝ) (hw : ∀ b, 0 ≤ w b)
    (m : ℝ) (hm : 0 < m) (hmEq : Q.expect w = m) (a : α) (b : β) :
    (weightedLaw (FinProb.prod P Q) (fun z => w z.2) (fun z => hw z.2) m hm
        (by
          calc
            (FinProb.prod P Q).expect (fun z => w z.2) =
                P.expect (fun _ => Q.expect w) := prod_expect P Q (fun _ b => w b)
            _ = m := by rw [expect_const, hmEq])).w (a, b) =
      (FinProb.prod P (weightedLaw Q w hw m hm hmEq)).w (a, b) := by
  simp only [weightedLaw, FinProb.prod]
  field_simp [hm.ne']

private theorem delta_small {p : ℝ} (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.exp (-(n : ℝ) ^ (p / 2)) ≤ 1 / 4 := by
  have hrpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (p / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < p / 2)).comp
      tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, Real.log 4 ≤ (n : ℝ) ^ (p / 2) :=
    hrpow.eventually (eventually_ge_atTop (Real.log 4))
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨n₀, ?_⟩
  intro n hn
  have hlog : Real.log 4 ≤ (n : ℝ) ^ (p / 2) := hn₀ n hn
  calc
    Real.exp (-(n : ℝ) ^ (p / 2)) ≤ Real.exp (-Real.log 4) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = 1 / 4 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      norm_num

theorem bcomp_tail (η₀ γ β p K : ℝ) (h : ℕ) (cH : ℝ) (hcH : 0 < cH)
    (hη₀ : 0 < η₀) (hβτ : β < tau8 η₀ / 4) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N),
      Std D γ K X Y R → GridFacts η₀ D.n → CondProductBound →
      D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) → D.BcompMean K →
      D.hiddenLaw.pr (fun Θ => ¬ D.CompOK (8 * (40 * K + 1)) Θ) ≤
        (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  classical
  obtain ⟨ncap, hcap⟩ := bcompCap_small η₀ β K h hη₀ hβτ hK
  obtain ⟨ncharge, hcharge⟩ := bcompChargeSmall η₀ cH hη₀ hcH
  refine ⟨max ncap ncharge, ?_⟩
  intro D hn X Y R hStd hGF hCP hLLL hBM
  have hncap : ncap ≤ D.n := le_trans (le_max_left _ _) hn
  have hncharge : ncharge ≤ D.n := le_trans (le_max_right _ _) hn
  let L : ℝ := bcompCap η₀ β K h D.n
  let Z : EvenRole D.n → Fin D.N → D.Hist → ℝ := fun a x Θ =>
    D.Bcomp Θ (keyOf η₀ a.1) x
  let d : EvenRole D.n → Fin D.N → ℝ := fun _ _ => 40 * K
  have hroleCard : 0 < Fintype.card (EvenRole D.n) := by
    rw [hGF.even_card]
    positivity
  letI : Nonempty (EvenRole D.n) := Fintype.card_pos_iff.mp hroleCard
  have hchargeSmall : 4 * Real.exp (-(D.n : ℝ) ^ cH) * (D.n : ℝ) *
      (1 + ((2 * sC η₀ D.n + 1) ^ 4 : ℕ)) ≤ 1 / 4 := hcharge D.n hncharge
  have hnpos : 0 < D.n := lt_of_lt_of_le (by norm_num) hGF.pos.1
  have hL : 0 ≤ L := by
    dsimp [L, bcompCap]
    positivity
  have hZ0 : ∀ a x Θ, 0 ≤ Z a x Θ := by
    intro a x Θ
    exact bcomp_nonneg D Θ (keyOf η₀ a.1) x
  have hZL : ∀ a x Θ, Θ ∈ Finset.univ → Z a x Θ ≤ L := by
    intro a x Θ _
    by_cases hb : D.BaseGates Θ (keyOf η₀ a.1)
    · simpa [Z, L] using bcomp_le_cap D X Y R hStd hGF Θ (keyOf η₀ a.1) x hb
    · simp [Z, L, Ctx.Bcomp, hb, hL]
  have hself : ∀ a : EvenRole D.n, a ∈ evenKeyNear η₀ 8 a := by
    intro a
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hdist : keyDist (keyOf η₀ a.1) (keyOf η₀ a.1) = 0 := by simp [keyDist]
    rw [hdist]
    norm_num
  have hf : 0 ≤ fGrid η₀ D.n := by
    unfold fGrid
    positivity
  have hnear : ∀ a : EvenRole D.n,
      ((evenKeyNear η₀ 8 a).card : ℝ) ≤ fGrid η₀ D.n * Fintype.card (EvenRole D.n) :=
    hGF.near_even
  have hD0 : 0 ≤ 40 * K := by positivity
  have hmean : ∀ x : Fin D.N,
      (Fintype.card (EvenRole D.n) : ℝ)⁻¹ * ∑ a, d a x ≤ 40 * K := by
    intro x
    have hsum : (∑ a : EvenRole D.n, d a x) =
        (Fintype.card (EvenRole D.n) : ℝ) * (40 * K) := by
      simp [d, nsmul_eq_mul]
    have hcard : (Fintype.card (EvenRole D.n) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hroleCard)
    rw [hsum]
    field_simp [hcard]
    norm_num
  have hsmall : (D.n : ℝ) * fGrid η₀ D.n * L ≤ 1 := by
    simpa [L] using hcap D.n hncap
  have hlabels : (Fintype.card (Fin D.N) : ℝ) ≤ (D.n : ℝ) * 2 ^ D.n := by
    rw [Fintype.card_fin]
    exact_mod_cast hStd.size.2
  have hjoint : ∀ (x : Fin D.N) (m : ℕ), m ≤ D.n → ∀ s : Fin m → EvenRole D.n,
      (∀ i j : Fin m, j < i → s i ∉ evenKeyNear η₀ 8 (s j)) →
        ∑ Θ ∈ Finset.univ, D.hiddenLaw.w Θ * ∏ i, Z (s i) x Θ ≤
          (2 : ℝ) ^ m * ∏ i, d (s i) x := by
    intro x m hm s hsep
    have hcost := bcomp_touch_cost (γ := γ) (K := K) D hGF hη₀ hcH hLLL s hm hchargeSmall hsep
    have hmoment := bcomp_joint_of_cost D X Y R hStd hBM hGF hCP hK
      (2 * Real.exp (-(D.n : ℝ) ^ cH)) hLLL s x hsep hcost
    simpa [FinProb.expect, Z, d, Finset.prod_const] using hmoment
  have hthreshold : 4 * (2 : ℝ) * (40 * K + 1) = 8 * (40 * K + 1) := by
    ring
  have htail := HypercubeRamsey.scatteredMoments_union_labels D.hiddenLaw Finset.univ Z hZ0 L hL hZL
    (evenKeyNear η₀ 8) hself (fGrid η₀ D.n) hf hnear D.n hnpos 2 (40 * K)
    (by norm_num) hD0 d (by intro a x; exact hD0) hmean hjoint hsmall hlabels
  rw [hthreshold] at htail
  simp only [Finset.mem_univ, true_and] at htail
  have hbad : ∀ Θ : D.Hist,
      (¬ D.CompOK (8 * (40 * K + 1)) Θ) ↔
        ∃ x, 8 * (40 * K + 1) < (Fintype.card (EvenRole D.n) : ℝ)⁻¹ *
          ∑ a : EvenRole D.n, D.Bcomp Θ (keyOf η₀ a.1) x := by
    intro Θ
    simp [Ctx.CompOK, not_forall]
  rw [FinProb.pr]
  simpa only [hbad] using htail

theorem bcomp_mean (η₀ γ β p K : ℝ) (h : ℕ) (hη₀ : 0 < η₀) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N),
      Std D γ K X Y R → GridFacts η₀ D.n → D.BcompMean K := by
  obtain ⟨nsmall, hnsmall⟩ := cross_survival_small η₀ hη₀
  refine ⟨nsmall, ?_⟩
  intro D hn X Y R hStd hGF g x
  by_cases hx : x ∈ R
  · let k : ℕ := (crossKeys g).card
    let base : ℝ := ((2 : ℝ) ^ h)⁻¹
    let δ : ℝ := (D.n : ℝ) ^ (-(eta8 η₀ / 2))
    have hq : D.R'.pr (fun θ => D.hitsAll x θ) ≤ base * (1 + δ) := by
      have hsurv := hStd.survival x hx
      have hqeq := rprime_hits_pr D x
      rw [← hqeq] at hsurv
      have hu := (abs_le.mp hsurv).2
      dsimp [base, δ]
      linarith
    have hqnonneg : 0 ≤ D.R'.pr (fun θ => D.hitsAll x θ) :=
      S08.pr_nonneg _ _
    have hδ : 0 ≤ δ := by positivity
    have hk : (k : ℝ) ≤ 2 * (sC η₀ D.n : ℝ) := by
      dsimp [k]
      exact_mod_cast hGF.crossKeys_card g
    have hkδ : (k : ℝ) * δ ≤ Real.log (11 / 10 : ℝ) := by
      calc
        (k : ℝ) * δ ≤ 2 * (sC η₀ D.n : ℝ) * δ :=
          mul_le_mul_of_nonneg_right hk hδ
        _ ≤ Real.log (11 / 10 : ℝ) := hnsmall D.n hn
    have hpow : (1 + δ) ^ k ≤ 11 / 10 := by
      have hbasele : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
      calc
        (1 + δ) ^ k ≤ (Real.exp δ) ^ k :=
          pow_le_pow_left₀ (by positivity) hbasele k
        _ = Real.exp ((k : ℝ) * δ) := by
          exact (Real.exp_nat_mul δ k).symm
        _ ≤ Real.exp (Real.log (11 / 10 : ℝ)) := Real.exp_le_exp.mpr hkδ
        _ = 11 / 10 := Real.exp_log (by norm_num)
    have hAG : 0 < D.AG g := by unfold Ctx.AG; positivity
    have hbasepow : base ^ k = D.AG g := by
      simp [base, Ctx.AG, k, inv_pow, pow_mul]
    have hqpow : (D.R'.pr (fun θ => D.hitsAll x θ)) ^ k ≤ (11 / 10 : ℝ) * D.AG g := by
      calc
        _ ≤ (base * (1 + δ)) ^ k :=
          pow_le_pow_left₀ hqnonneg hq k
        _ = base ^ k * (1 + δ) ^ k := mul_pow _ _ _
        _ ≤ D.AG g * (11 / 10 : ℝ) := by
          rw [hbasepow]
          exact mul_le_mul_of_nonneg_left hpow (le_of_lt hAG)
        _ = (11 / 10 : ℝ) * D.AG g := by ring
    let A : D.Hist → ℝ := fun Θ => if D.BaseGates Θ g then 1 else 0
    let Hc : D.Hist → ℝ := fun Θ => if D.crossHit Θ g x then 1 else 0
    let F : D.Hist → ℝ := fun Θ =>
      ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)
    have hAnonneg (Θ : D.Hist) : 0 ≤ A Θ := by
      dsimp [A]
      split_ifs <;> norm_num
    have hFnonneg (Θ : D.Hist) : 0 ≤ F Θ := by
      dsimp [F]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (D.postW_nonneg _ _) (mul_nonneg (by positivity) ((D.M.μ i).nonneg x))
    have hHnonneg (Θ : D.Hist) : 0 ≤ Hc Θ := by
      dsimp [Hc]
      split_ifs <;> norm_num
    have hcross_dep : FinProb.DependsOn Hc (crossKeys g) := by
      intro Θ Θ' hEq
      have hlogic : D.crossHit Θ g x = D.crossHit Θ' g x := by
        apply propext
        constructor
        · intro hh u hu
          have ht := hEq u hu
          rw [← ht]
          exact hh u hu
        · intro hh u hu
          have ht := hEq u hu
          rw [ht]
          exact hh u hu
      simp [Hc, hlogic]
    have hown_dep : FinProb.DependsOn F {g} := by
      intro Θ Θ' hEq
      have ht := hEq g (by simp)
      dsimp [F]
      rw [ht]
    have hgn : g ∉ crossKeys g := by
      have hself : keyDist g g = 0 := by simp [keyDist]
      simp [crossKeys, hself]
    have hdisj : Disjoint (crossKeys g) ({g} : Finset D.KeyT) :=
      Finset.disjoint_singleton_right.mpr hgn
    have hfactor : D.rawHidden.expect (fun Θ => Hc Θ * F Θ) =
        D.rawHidden.expect Hc * D.rawHidden.expect F := by
      change (FinProb.pi (fun _ : D.KeyT => D.R')).expect (fun Θ => Hc Θ * F Θ) = _
      exact FinProb.pi_expect_mul_of_disjoint (fun _ : D.KeyT => D.R') Hc F
        (crossKeys g) {g} hcross_dep hown_dep hdisj
    have hFmean : D.rawHidden.expect F =
        (D.N : ℝ) * ∑ i, D.M.Λ i * (D.M.μ i).w x := by
      dsimp [F]
      unfold FinProb.expect
      calc
        (∑ Θ, D.rawHidden.w Θ *
            ∑ i, D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) =
            ∑ Θ, ∑ i, D.rawHidden.w Θ *
              (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by
          apply Finset.sum_congr rfl
          intro Θ _
          rw [Finset.mul_sum]
        _ = ∑ i, ∑ Θ, D.rawHidden.w Θ *
              (D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by rw [Finset.sum_comm]
        _ = ∑ i, D.rawHidden.expect
              (fun Θ => D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) := by rfl
        _ = ∑ i, ((D.N : ℝ) * (D.M.μ i).w x) * D.M.Λ i := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            D.rawHidden.expect (fun Θ => D.postW (Θ g) i * ((D.N : ℝ) * (D.M.μ i).w x)) =
                D.rawHidden.expect (fun Θ => ((D.N : ℝ) * (D.M.μ i).w x) * D.postW (Θ g) i) := by
              apply expect_congr
              intro Θ
              ring
            _ = ((D.N : ℝ) * (D.M.μ i).w x) * D.rawHidden.expect
                (fun Θ => D.postW (Θ g) i) := FinProb.expect_smul _ _ _
            _ = ((D.N : ℝ) * (D.M.μ i).w x) * D.M.Λ i := by
              rw [raw_postW_expect]
        _ = (D.N : ℝ) * ∑ i, D.M.Λ i * (D.M.μ i).w x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    have hFmeanBound : D.rawHidden.expect F ≤ 4 * K := by
      rw [hFmean]
      exact hStd.bal.1 x
    have hBpoint (Θ : D.Hist) : D.Bcomp Θ g x ≤
        (8 * (D.AG g)⁻¹) * (Hc Θ * F Θ) := by
      have hAle : A Θ ≤ 1 := by dsimp [A]; split_ifs <;> norm_num
      have hAterm : A Θ * (Hc Θ * F Θ) ≤ Hc Θ * F Θ := by
        calc
          A Θ * (Hc Θ * F Θ) ≤ 1 * (Hc Θ * F Θ) :=
            mul_le_mul_of_nonneg_right hAle (mul_nonneg (hHnonneg Θ) (hFnonneg Θ))
          _ = Hc Θ * F Θ := by ring
      have hc : 0 ≤ 8 * (D.AG g)⁻¹ := by positivity
      have hrewrite : D.Bcomp Θ g x = (8 * (D.AG g)⁻¹) * (A Θ * (Hc Θ * F Θ)) := by
        unfold Ctx.Bcomp
        by_cases hb : D.BaseGates Θ g <;> by_cases hh : D.crossHit Θ g x
        <;> simp [A, Hc, F, hb, hh] <;> ring
      rw [hrewrite]
      exact mul_le_mul_of_nonneg_left hAterm hc
    have hBexpect : D.rawHidden.expect (fun Θ => D.Bcomp Θ g x) ≤
        (8 * (D.AG g)⁻¹) * D.rawHidden.expect (fun Θ => Hc Θ * F Θ) := by
      calc
        D.rawHidden.expect (fun Θ => D.Bcomp Θ g x) ≤
            D.rawHidden.expect (fun Θ => (8 * (D.AG g)⁻¹) * (Hc Θ * F Θ)) :=
          FinProb.expect_mono D.rawHidden hBpoint
        _ = (8 * (D.AG g)⁻¹) * D.rawHidden.expect (fun Θ => Hc Θ * F Θ) :=
          FinProb.expect_smul _ _ _
    have hHmean : D.rawHidden.expect Hc =
        (D.R'.pr (fun θ => D.hitsAll x θ)) ^ k := by
      calc
        D.rawHidden.expect Hc = D.rawHidden.pr (fun Θ => D.crossHit Θ g x) := by
          simpa [Hc] using (FinProb.pr_indicator D.rawHidden (fun Θ => D.crossHit Θ g x)).symm
        _ = _ := cross_hit_pr D g x
    have hfactorbound : D.rawHidden.expect Hc * D.rawHidden.expect F ≤
        ((11 / 10 : ℝ) * D.AG g) * (4 * K) := by
      have hFmeanNonneg := expect_nonneg D.rawHidden F hFnonneg
      calc
        D.rawHidden.expect Hc * D.rawHidden.expect F ≤
            ((11 / 10 : ℝ) * D.AG g) * D.rawHidden.expect F := by
          rw [hHmean]
          exact mul_le_mul_of_nonneg_right hqpow hFmeanNonneg
        _ ≤ ((11 / 10 : ℝ) * D.AG g) * (4 * K) :=
          mul_le_mul_of_nonneg_left hFmeanBound (by positivity)
    have hbound : D.rawHidden.expect (fun Θ => D.Bcomp Θ g x) ≤ 40 * K := by
      have hc : 0 ≤ 8 * (D.AG g)⁻¹ := by positivity
      calc
        D.rawHidden.expect (fun Θ => D.Bcomp Θ g x) ≤
            (8 * (D.AG g)⁻¹) * D.rawHidden.expect (fun Θ => Hc Θ * F Θ) := hBexpect
        _ = (8 * (D.AG g)⁻¹) * (D.rawHidden.expect Hc * D.rawHidden.expect F) := by
          rw [hfactor]
        _ ≤
            8 * (D.AG g)⁻¹ * (((11 / 10 : ℝ) * D.AG g) * (4 * K)) :=
          mul_le_mul_of_nonneg_left hfactorbound hc
        _ ≤ 40 * K := by
          have hcancel :
              8 * (D.AG g)⁻¹ * (((11 / 10 : ℝ) * D.AG g) * (4 * K)) =
                (8 * (11 / 10) * 4) * K := by field_simp [ne_of_gt hAG]
          rw [hcancel]
          nlinarith [hK]
    simpa [Ctx.BcompMean] using hbound
  · have hzero (Θ : D.Hist) : D.Bcomp Θ g x = 0 := by
      by_cases hbase : D.BaseGates Θ g
      · have hFzero : ∑ i, D.postW (Θ g) i *
            ((D.N : ℝ) * (D.M.μ i).w x) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          by_cases hLam : 0 < D.M.Λ i
          · have hμ := (hStd.laws i hLam).1 x hx
            simp [hμ]
          · have hLamZero : D.M.Λ i = 0 := by linarith [D.M.Λ_nonneg i]
            have hpostle : D.postW (Θ g) i ≤ 0 := by
              have hgate := hbase.1 i
              simpa [hLamZero] using hgate
            have hpostzero : D.postW (Θ g) i = 0 :=
              le_antisymm hpostle (D.postW_nonneg _ _)
            simp [hpostzero]
        unfold Ctx.Bcomp
        rw [if_pos hbase]
        simp [hFzero]
      · unfold Ctx.Bcomp
        rw [if_neg hbase]
    have hmean0 : D.rawHidden.expect (fun Θ => D.Bcomp Θ g x) = 0 := by
      simp [FinProb.expect, hzero]
    rw [hmean0]
    nlinarith [hK]

private theorem pre_pr_reassoc {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)
    (E : D.Hist → D.Pos × D.TAT → Prop) :
    D.preLaw.pr (fun q => E q.1.1 (q.1.2, q.2)) =
      (FinProb.bind D.hiddenLaw (fun Θ => FinProb.bind D.posLaw (fun _ => D.rawTAT Θ))).pr
        (fun q => E q.1 q.2) := by
  classical
  have hleft : D.preLaw.pr (fun q => E q.1.1 (q.1.2, q.2)) =
      ∑ Θ, D.hiddenLaw.w Θ *
        (FinProb.bind D.posLaw (fun P => D.rawTAT Θ)).pr (fun z => E Θ z) := by
    unfold Ctx.preLaw
    rw [pr_bind_eq]
    calc
      (∑ q : D.Hist × D.Pos,
          (FinProb.bind D.hiddenLaw (fun _ => D.posLaw)).w q *
            (D.rawTAT q.1).pr (fun ω => E q.1 (q.2, ω))) =
        ∑ Θ, ∑ P, (D.hiddenLaw.w Θ * D.posLaw.w P) *
            (D.rawTAT Θ).pr (fun ω => E Θ (P, ω)) := by
          simp only [FinProb.bind]
          rw [Fintype.sum_prod_type]
      _ = ∑ Θ, D.hiddenLaw.w Θ *
            (FinProb.bind D.posLaw (fun P => D.rawTAT Θ)).pr (fun z => E Θ z) := by
          apply Finset.sum_congr rfl
          intro Θ _
          rw [pr_bind_eq]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro P _
          ring
  have hright :
      (FinProb.bind D.hiddenLaw (fun Θ => FinProb.bind D.posLaw (fun _ => D.rawTAT Θ))).pr
        (fun q => E q.1 q.2) =
      ∑ Θ, D.hiddenLaw.w Θ *
        (FinProb.bind D.posLaw (fun _ => D.rawTAT Θ)).pr (fun z => E Θ z) := by
    rw [pr_bind_eq]
  rw [hleft, hright]

theorem load_tail {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (C₁ C₂ a b : ℝ) (hb : 0 ≤ b)
    (hpos : 0 < D.rawHidden.pr (fun Θ => ∀ g, ¬ D.HBad Θ g))
    (hcomp : D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) ≤ a)
    (hcenter : ∀ Θ : D.Hist, (∀ g, ¬ D.HBad Θ g) → D.CompOK C₁ Θ →
      (FinProb.bind D.posLaw fun _ => D.rawTAT Θ).pr
        (fun z => D.SelOK ((Θ, z.1), z.2) ∧ ¬ D.LoadOK C₂ ((Θ, z.1), z.2)) ≤ b) :
    D.preLaw.pr (fun q => D.SelOK q ∧ ¬ D.LoadOK C₂ q) ≤ a + b := by
  classical
  let Good : D.Hist → Prop := fun Θ => ∀ g, ¬ D.HBad Θ g
  let E : D.Hist → D.Pos × D.TAT → Prop := fun Θ z =>
    D.SelOK ((Θ, z.1), z.2) ∧ ¬ D.LoadOK C₂ ((Θ, z.1), z.2)
  let K : D.Hist → FinProb (D.Pos × D.TAT) :=
    fun Θ => FinProb.bind D.posLaw (fun _ => D.rawTAT Θ)
  have hform (Θ : D.Hist) : D.hiddenLaw.w Θ =
      (if Good Θ then D.rawHidden.w Θ else 0) / D.rawHidden.pr Good := by
    change (condOr D.rawHidden Good).w Θ = _
    unfold condOr
    rw [dif_pos hpos]
    by_cases hg : Good Θ <;> simp [FinProb.cond, hg]
  have hsupp (Θ : D.Hist) (hw : D.hiddenLaw.w Θ ≠ 0) : Good Θ := by
    by_contra hbad
    have hzero : D.hiddenLaw.w Θ = 0 := by
      rw [hform]
      simp [hbad]
    exact hw hzero
  have hpoint : ∀ Θ, D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z) ≤
      (if ¬ D.CompOK C₁ Θ then D.hiddenLaw.w Θ else 0) + D.hiddenLaw.w Θ * b := by
    intro Θ
    by_cases hC : D.CompOK C₁ Θ
    · by_cases hw : D.hiddenLaw.w Θ = 0
      · simp [hw]
      · have hraw : (K Θ).pr (fun z => E Θ z) ≤ b := by
          simpa [K, E] using hcenter Θ (hsupp Θ hw) hC
        simpa [hC] using mul_le_mul_of_nonneg_left hraw (D.hiddenLaw.nonneg Θ)
    · have hle := pr_le_one (K Θ) (fun z => E Θ z)
      have hw := D.hiddenLaw.nonneg Θ
      have hwb : 0 ≤ D.hiddenLaw.w Θ * b := mul_nonneg hw hb
      have hle' : D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z) ≤ D.hiddenLaw.w Θ := by
        simpa using mul_le_mul_of_nonneg_left hle hw
      have hsum : D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z) ≤
          D.hiddenLaw.w Θ + D.hiddenLaw.w Θ * b :=
        hle'.trans (le_add_of_nonneg_right hwb)
      simpa [hC] using hsum
  have hbound :
      (FinProb.bind D.hiddenLaw K).pr (fun q => E q.1 q.2) ≤
        D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) + b := by
    rw [pr_bind_eq]
    calc
      (∑ Θ, D.hiddenLaw.w Θ * (K Θ).pr (fun z => E Θ z)) ≤
        ∑ Θ, ((if ¬ D.CompOK C₁ Θ then D.hiddenLaw.w Θ else 0) + D.hiddenLaw.w Θ * b) :=
          Finset.sum_le_sum fun Θ _ => hpoint Θ
      _ = D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) + b := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, D.hiddenLaw.sum_eq_one]
          rw [FinProb.pr]
          ring
  have heq := pre_pr_reassoc D E
  rw [heq]
  calc
    (FinProb.bind D.hiddenLaw K).pr (fun q => E q.1 q.2) ≤
        D.hiddenLaw.pr (fun Θ => ¬ D.CompOK C₁ Θ) + b := hbound
    _ ≤ a + b := by linarith [hcomp]

set_option maxHeartbeats 5000000 in
theorem select_mean (η₀ β p : ℝ) (h : ℕ) (hη₀ : 0 < η₀) (hp : 0 < p)
    (hadm : HDAdmissible 10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀)
      (thetaH η₀) (aH η₀) (1 / 2) 1 2) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.SelectMean := by
  classical
  obtain ⟨c, hc, nHeight, hHeightAll⟩ := HypercubeRamsey.height_selection_positive
    10 (b0H η₀) (bH η₀) (sigmaH η₀) (zetaH η₀) (thetaH η₀) (aH η₀) (1 / 2) 1 2
    hadm (hdRegime η₀)
  obtain ⟨nDelta, hDeltaSmall⟩ := delta_small hp
  rcases hadm.hsz with ⟨hσ, hσζ, hζ, _hθ, _hθ₁⟩
  obtain ⟨nScale, hScale⟩ := topScale_sq_bound (sigmaH η₀) (zetaH η₀) hσ hσζ hζ
  obtain ⟨nPoly, hPoly⟩ := exp_poly_small c hc 12
  let n₀ := max 1 (max nHeight (max nDelta (max nScale nPoly)))
  refine ⟨n₀, ?_⟩
  intro D hn hGF
  intro Θ hgood e x
  let p₀ := hdP η₀ D.n
  let g : D.KeyT := e.1
  have hnHeight : nHeight ≤ D.n := by dsimp [n₀] at hn; omega
  have hnDelta : nDelta ≤ D.n := by dsimp [n₀] at hn; omega
  have hnScale : nScale ≤ D.n := by dsimp [n₀] at hn; omega
  have hnPoly : nPoly ≤ D.n := by dsimp [n₀] at hn; omega
  have hLamPos : 0 < p₀.lam := by
    have hnpos : (0 : ℝ) < (D.n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) hGF.pos.1)
    simpa [p₀, hdP, Real.rpow_natCast] using (Real.rpow_pos_of_pos hnpos (10 : ℝ))
  have hVball : (Finset.univ.filter (fun u : CubeVertex p₀.d =>
      hammingDist u e.2 ≤ p₀.r)).Nonempty := by
    refine ⟨e.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    change hammingDist e.2 e.2 ≤ p₀.r
    unfold hammingDist
    simp
  have hVnat : 0 < p₀.V := by
    unfold HDParams.V
    rw [← loadHammingBallCard p₀.d p₀.r e.2]
    exact Finset.card_pos.mpr hVball
  have hVpos : (0 : ℝ) < (p₀.V : ℝ) := by exact_mod_cast hVnat
  let presentMass : ℝ := max 0 (min (p₀.lam / (p₀.V : ℝ)) 1)
  have hpresenceNonneg : 0 ≤ presentMass := le_max_left _ _
  have hLamVNonneg : 0 ≤ p₀.lam / (p₀.V : ℝ) := div_nonneg hLamPos.le hVpos.le
  have hpresenceLe : presentMass ≤ p₀.lam / (p₀.V : ℝ) :=
    max_le hLamVNonneg (min_le_left _ _)
  have hΔ : D.Δ ≤ 1 / 4 := by
    simpa [Ctx.Δ] using hDeltaSmall D.n hnDelta
  have hbase : D.BaseGates Θ g := by
    by_contra hb
    exact hgood g (by simp [Ctx.HBad, hb])
  let mass : ℝ := (D.tilt Θ g).expect
    (fun i => (D.N : ℝ) * (D.anchorU Θ g i).w x)
  have hmassNonneg : 0 ≤ mass := by
    apply expect_nonneg
    intro i
    exact mul_nonneg (by positivity) ((D.anchorU Θ g i).nonneg x)
  have hmassBound : mass ≤ D.Bcomp Θ g x / 4 := by
    simpa [mass] using tilt_anchor_mass D Θ g x hbase hΔ
  have hScaleD : p₀.H ≤ 8 * D.n ^ 2 := by
    simpa [p₀, hdP, HH] using hScale D.n hnScale
  have hScaleCast : (p₀.H : ℝ) ≤ 8 * (D.n : ℝ) ^ 2 := by exact_mod_cast hScaleD
  have hLamCast : p₀.lam = (D.n : ℝ) ^ 10 := by
    simpa [p₀, hdP] using (Real.rpow_natCast (D.n : ℝ) 10)
  have hPolyD : (D.n : ℝ) ^ 12 * Real.exp (-(D.n : ℝ) ^ c) ≤ 1 / 64 :=
    hPoly D.n hnPoly
  have hHeightTail : (p₀.H : ℝ) * p₀.lam * Real.exp (-(D.n : ℝ) ^ c) ≤ 1 / 8 := by
    calc
      (p₀.H : ℝ) * p₀.lam * Real.exp (-(D.n : ℝ) ^ c) ≤
          (8 * (D.n : ℝ) ^ 2) * ((D.n : ℝ) ^ 10) * Real.exp (-(D.n : ℝ) ^ c) := by
            have hscaleLam : (p₀.H : ℝ) * p₀.lam ≤
                (8 * (D.n : ℝ) ^ 2) * ((D.n : ℝ) ^ 10) := by
              calc
                (p₀.H : ℝ) * p₀.lam ≤ (8 * (D.n : ℝ) ^ 2) * p₀.lam :=
                  mul_le_mul_of_nonneg_right hScaleCast hLamPos.le
                _ = (8 * (D.n : ℝ) ^ 2) * ((D.n : ℝ) ^ 10) := by rw [hLamCast]
            exact mul_le_mul_of_nonneg_right hscaleLam (by positivity)
      _ = 8 * ((D.n : ℝ) ^ 2 * (D.n : ℝ) ^ 10) * Real.exp (-(D.n : ℝ) ^ c) := by ring
      _ = 8 * (D.n : ℝ) ^ 12 * Real.exp (-(D.n : ℝ) ^ c) := by
        have hpow : (D.n : ℝ) ^ 2 * (D.n : ℝ) ^ 10 = (D.n : ℝ) ^ 12 := by
          rw [← pow_add]
        rw [hpow]
      _ ≤ 8 * (1 / 64 : ℝ) := by
        calc
          8 * (D.n : ℝ) ^ 12 * Real.exp (-(D.n : ℝ) ^ c) =
              8 * ((D.n : ℝ) ^ 12 * Real.exp (-(D.n : ℝ) ^ c)) := by ring
          _ ≤ 8 * (1 / 64 : ℝ) :=
            mul_le_mul_of_nonneg_left hPolyD (by norm_num : (0 : ℝ) ≤ (8 : ℝ))
      _ = 1 / 8 := by norm_num
  have hHeightParams := hHeightAll p₀ rfl rfl rfl rfl rfl hnHeight
    (by simpa [p₀, hdP] using hGF.hd_ok.2.1)
    (by simpa [p₀, hdP] using hGF.hd_ok.2.2)
    (by simpa [p₀, hdP, hdRegime] using hGF.hd_ok.1)
  have hTermBound (ℓ : D.Loc) :
      D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
        selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) ≤
        presentMass * mass * (if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)) := by
    let Slice := p₀.Loc → Bool
    let Tags := D.Tags
    let Acts := p₀.Loc → Bool
    let Ties := p₀.Ties
    let tagLaw : FinProb Tags := D.tagLawAll Θ
    let w : Tags → ℝ := fun t => (D.N : ℝ) * (D.anchorU Θ g (t g ℓ)).w x
    let ps : FinProb Slice := p₀.posLawForced (some ℓ)
    let otherLaw : FinProb (PosOutside D g) := FinProb.pi fun _ => p₀.posLaw
    let actLaw : FinProb Acts := p₀.actLaw
    let tieLaw : FinProb Ties := p₀.tieLaw
    let actTie : FinProb (Acts × Ties) := FinProb.prod actLaw tieLaw
    let joint : FinProb (Slice × Tags) := FinProb.prod ps tagLaw
    have hw (t : Tags) : 0 ≤ w t := by
      exact mul_nonneg (by positivity) ((D.anchorU Θ g (t g ℓ)).nonneg x)
    have hmTag : tagLaw.expect w = mass := by
      simpa [tagLaw, w, mass, g] using tag_anchor_expect D Θ g ℓ x
    have hJointMean : joint.expect (fun z => w z.2) = mass := by
      calc
        joint.expect (fun z => w z.2) = ps.expect (fun _ => tagLaw.expect w) :=
          prod_expect ps tagLaw (fun _ t => w t)
        _ = mass := by rw [expect_const, hmTag]
    let rate : ℝ := if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)
    have hForcedBound :
        (FinProb.prod otherLaw ps).expect (fun z =>
          (D.rawTAT Θ).expect (fun ω =>
            selectedCenterTerm D Θ e x (reconstructPos D g z.2 z.1) ω.1.1
              (ω.1.2 e.1) (ω.2 e.1) ℓ)) ≤ mass * rate := by
      have hprod := prod_expect otherLaw ps (fun O P =>
        (D.rawTAT Θ).expect (fun ω =>
          selectedCenterTerm D Θ e x (reconstructPos D g P O) ω.1.1
            (ω.1.2 e.1) (ω.2 e.1) ℓ))
      rw [hprod]
      apply expect_le_const
      intro O
      let fullPos : Slice → D.Pos := fun P => reconstructPos D g P O
      let elig : Slice → Tags → p₀.EligMap := fun P t => D.elig Θ (fullPos P) t g
      let Pick : (Slice × Tags) → Acts → Ties → Prop := fun z A τ =>
        D.LocalLegal Θ (fullPos z.1) z.2 e ∧
          p₀.selection Finset.univ ((fullPos z.1) g) A (D.elig Θ (fullPos z.1) z.2 g) τ e.2 = some ℓ
      let HeightEvent : (Slice × Tags) → Acts → Prop := fun z A =>
        p₀.Legal z.1 (elig z.1 z.2) (p₀.domBall Finset.univ e.2 p₀.Rlong) ∧
          0 < p₀.height Finset.univ z.1 A (elig z.1 z.2) p₀.Rlong e.2
      have hlocalLegal (P : Slice) (t : Tags) (hL : D.LocalLegal Θ (fullPos P) t e) :
          p₀.Legal P (elig P t) (p₀.domBall Finset.univ e.2 p₀.Rlong) := by
        change p₀.Legal ((fullPos P) g) (D.elig Θ (fullPos P) t g)
          (p₀.domBall Finset.univ e.2 p₀.Rlong) at hL
        have hkey : (fullPos P) g = P := by
          simpa [fullPos] using reconstructPos_key D g P O
        rw [hkey] at hL
        simpa [elig] using hL
      have hselection (P : Slice) (t : Tags) (A : Acts) (τ : Ties)
          (hS : Pick (P, t) A τ) :
          p₀.selection Finset.univ P A (elig P t) τ e.2 = some ℓ := by
        have hkey := reconstructPos_key D g P O
        simpa [Pick, elig, fullPos, hkey] using hS.2
      have hlocToHeight (z : Slice × Tags) (A : Acts) (τ : Ties)
          (hS : Pick z A τ) (hℓ : 0 < ℓ.2.val) : HeightEvent z A := by
        have hlegal := hlocalLegal z.1 z.2 hS.1
        have hsel := hselection z.1 z.2 A τ hS
        have hlev := selected_level_of_local_legal Finset.univ (z.1)
          A (elig z.1 z.2) τ e.2 ℓ (by simp)
          hlegal hsel
        refine ⟨hlegal, ?_⟩
        rw [hlev]
        exact hℓ
      have hTieProb (hℓzero : ℓ.2.val = 0) (z : Slice × Tags) :
          actTie.pr (fun aτ => Pick z aτ.1 aτ.2) ≤ 3 / p₀.lam := by
        rcases z with ⟨P, t⟩
        by_cases hL : D.LocalLegal Θ (fullPos P) t e
        · have hlegal := hlocalLegal P t hL
          have hsite : e.2 ∈ p₀.domBall Finset.univ e.2 p₀.Rlong := by
            simp [HDParams.domBall]
          let j0 : Fin (p₀.H + 1) := ⟨0, by omega⟩
          have hlegal0 : p₀.LegalAt P (elig P t) e.2 j0 := hlegal e.2 hsite j0
          by_cases hmem0 : ℓ ∈ elig P t e.2 j0
          · have hIncl : ∀ aτ : Acts × Ties, Pick (P, t) aτ.1 aτ.2 →
                p₀.height Finset.univ P aτ.1 (elig P t) p₀.Rlong e.2 = 0 ∧
                  p₀.selection Finset.univ P aτ.1 (elig P t) aτ.2 e.2 = some ℓ := by
              intro aτ hS
              have hsel := hselection P t aτ.1 aτ.2 hS
              have hheight := selected_zero_height_of_local_legal Finset.univ
                P aτ.1 (elig P t) aτ.2 e.2 ℓ (by simp) hlegal hsel hℓzero
              exact ⟨hheight, hsel⟩
            calc
              actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2) ≤
                  actTie.pr (fun aτ => p₀.height Finset.univ P aτ.1
                    (elig P t) p₀.Rlong e.2 = 0 ∧
                    p₀.selection Finset.univ P aτ.1 (elig P t) aτ.2 e.2 = some ℓ) :=
                pr_mono actTie _ _ hIncl
              _ ≤ 3 / p₀.lam := HypercubeRamsey.height_selection_tie p₀ hLamPos
                P (elig P t) Finset.univ e.2 ℓ hlegal0 hmem0
          · have hempty : ∀ aτ : Acts × Ties, ¬ Pick (P, t) aτ.1 aτ.2 := by
              intro aτ hS
              have hsel := hselection P t aτ.1 aτ.2 hS
              have hlev := selected_level_of_local_legal Finset.univ P
                aτ.1 (elig P t) aτ.2 e.2 ℓ (by simp) hlegal hsel
              have hmem := selected_eligible Finset.univ P aτ.1 (elig P t)
                aτ.2 e.2 ℓ hsel
              have hH : p₀.height Finset.univ P aτ.1 (elig P t) p₀.Rlong e.2 < p₀.H := by
                by_contra hh
                simp [HDParams.selection, HDParams.selectionAt, hh] at hsel
              let j : Fin (p₀.H + 1) := ⟨p₀.height Finset.univ P aτ.1
                (elig P t) p₀.Rlong e.2, by omega⟩
              have hmem' : ℓ ∈ elig P t e.2 j := by simpa [j] using hmem
              have hj : j = j0 := Fin.ext (by simp [j, j0, hlev, hℓzero])
              exact hmem0 (by simpa [hj] using hmem')
            have hzeroProb : actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2) = 0 := by
              unfold FinProb.pr
              simp [hempty]
            rw [hzeroProb]
            positivity
        · have hempty : ∀ aτ : Acts × Ties, ¬ Pick (P, t) aτ.1 aτ.2 := by
            intro aτ hS
            exact hL hS.1
          have hzeroProb : actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2) = 0 := by
            unfold FinProb.pr
            simp [hempty]
          rw [hzeroProb]
          positivity
      by_cases hmassZero : mass = 0
      · have hzero := weighted_product_expect_pr_zero joint actTie
          (fun z => w z.2) (fun z => hw z.2) mass hJointMean hmassZero
          (fun z aτ => Pick (z.1, z.2) aτ.1 aτ.2)
        have hrawEq (P : Slice) :
            (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
              (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ) =
            tagLaw.expect (fun t => w t * actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2)) := by
          let Event : Tags → Acts × Ties → Prop := fun t aτ => Pick (P, t) aτ.1 aτ.2
          let f : Tags → Acts → Ties → ℝ := fun t A τ => by
            exact @ite ℝ (Event t (A, τ)) (Classical.propDecidable _) (w t) 0
          have hpoint (ω : D.TAT) :
              selectedCenterTerm D Θ e x (fullPos P) ω.1.1
                (ω.1.2 e.1) (ω.2 e.1) ℓ = f ω.1.1 (ω.1.2 e.1) (ω.2 e.1) := by
            have hselCompat (t : Tags) (A : Acts) (τ : Ties) :
                D.sel ((Θ, fullPos P), ((t, fun _ => A), fun _ => τ)) e =
                  p₀.selection Finset.univ ((fullPos P) g) A
                    (D.elig Θ (fullPos P) t g) τ e.2 := rfl
            have hcondition :
                (D.LocalLegal Θ (fullPos P) ω.1.1 e ∧
                  D.sel ((Θ, fullPos P), ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1)) e =
                    some ℓ) = Pick (P, ω.1.1) (ω.1.2 e.1) (ω.2 e.1) := by
              simp only [Pick]
              rw [hselCompat]
            dsimp [selectedCenterTerm, f]
            by_cases hsel : D.LocalLegal Θ (fullPos P) ω.1.1 e ∧
                D.sel ((Θ, fullPos P), ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1)) e =
                  some ℓ
            · have hpick := (Iff.of_eq hcondition).mp hsel
              have hevent : Event ω.1.1 (ω.1.2 e.1, ω.2 e.1) := by simpa [Event] using hpick
              simp [hsel, hevent, w, g]
            · have hnpick : ¬ Pick (P, ω.1.1) (ω.1.2 e.1) (ω.2 e.1) := by
                intro hpick
                exact hsel ((Iff.of_eq hcondition).mpr hpick)
              have hnevent : ¬ Event ω.1.1 (ω.1.2 e.1, ω.2 e.1) := by
                intro hevent
                apply hnpick
                simpa [Event] using hevent
              simp [hsel, hnevent]
          have hresult :
              (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
                (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ) =
                tagLaw.expect (fun t => w t * actTie.pr (Event t)) := by
            calc
              (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
                  (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ) =
                (D.rawTAT Θ).expect (fun ω => f ω.1.1 (ω.1.2 e.1) (ω.2 e.1)) :=
                  expect_congr _ _ _ hpoint
              _ = tagLaw.expect (fun t => actLaw.expect (fun A =>
                  tieLaw.expect (fun τ => f t A τ))) :=
                    rawTAT_expect_local_slices D Θ g f
              _ = tagLaw.expect (fun t => w t * actTie.pr (Event t)) := by
                    apply expect_congr
                    intro t
                    letI : ∀ aτ : Acts × Ties, Decidable (Event t aτ) :=
                      fun aτ => Classical.propDecidable _
                    calc
                      actLaw.expect (fun A => tieLaw.expect (fun τ => f t A τ)) =
                          actTie.expect (fun aτ =>
                            @ite ℝ (Event t aτ) (Classical.propDecidable _) (w t) 0) := by
                            exact (prod_expect actLaw tieLaw
                              (fun A τ => @ite ℝ (Event t (A, τ))
                                (Classical.propDecidable _) (w t) 0)).symm
                      _ = w t * actTie.pr (Event t) := expect_event_const actTie (Event t) (w t)
          simpa [Event] using hresult
        have hinnerEq :
            ps.expect (fun P => (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
              (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) =
            joint.expect (fun z => w z.2 * actTie.pr (fun aτ => Pick (z.1, z.2) aτ.1 aτ.2)) := by
          calc
            ps.expect (fun P => (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
              (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) =
            ps.expect (fun P => tagLaw.expect (fun t =>
                  w t * actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2))) := by
                    apply expect_congr
                    intro P
                    exact hrawEq P
            _ = joint.expect (fun z => w z.2 * actTie.pr (fun aτ => Pick (z.1, z.2) aτ.1 aτ.2)) :=
                  (prod_expect ps tagLaw
                    (fun P t => w t * actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2))).symm
        have hinner :
            ps.expect (fun P => (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
              (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) ≤ 0 := by
          rw [hinnerEq]
          exact hzero
        simpa [hmassZero, rate] using hinner
      · have hmassPos : 0 < mass := lt_of_le_of_ne hmassNonneg (Ne.symm hmassZero)
        let tagWeighted := weightedLaw tagLaw w hw mass hmassPos hmTag
        let jointWeighted := weightedLaw joint (fun z => w z.2)
          (fun z => hw z.2) mass hmassPos hJointMean
        have hweight (z : Slice × Tags) : jointWeighted.w z =
            (FinProb.prod ps tagWeighted).w z := by
          rcases z with ⟨P, t⟩
          simpa [jointWeighted, joint, tagWeighted] using
            weightedLaw_prod_right ps tagLaw w hw mass hmassPos hmTag P t
        have hprobFactor : (FinProb.prod jointWeighted actTie).pr
            (fun z => Pick (z.1.1, z.1.2) z.2.1 z.2.2) ≤ rate := by
          by_cases hzero : ℓ.2.val = 0
          · have hprob : (FinProb.prod jointWeighted actTie).pr
                (fun z => Pick (z.1.1, z.1.2) z.2.1 z.2.2) ≤ 3 / p₀.lam := by
              rw [prod_pr_integral jointWeighted actTie (fun u aτ => Pick u aτ.1 aτ.2)]
              exact expect_le_const jointWeighted
                (fun z => actTie.pr (fun aτ => Pick z aτ.1 aτ.2))
                (3 / p₀.lam) (fun z => hTieProb hzero z)
            simpa [rate, hzero] using hprob
          · have hℓpos : 0 < ℓ.2.val := Nat.pos_of_ne_zero hzero
            have hheightProb :
                (FinProb.prod (FinProb.prod ps tagWeighted) actLaw).pr
                  (fun z => HeightEvent z.1 z.2) ≤ Real.exp (-(D.n : ℝ) ^ c) := by
              change ((FinProb.prod (p₀.posLawForced (some ℓ)) tagWeighted).prod p₀.actLaw).pr
                (fun z => p₀.Legal z.1.1 (elig z.1.1 z.1.2)
                  (p₀.domBall Finset.univ e.2 p₀.Rlong) ∧
                  0 < p₀.height Finset.univ z.1.1 z.2
                    (elig z.1.1 z.1.2) p₀.Rlong e.2) ≤ Real.exp (-(D.n : ℝ) ^ c)
              exact hHeightParams Finset.univ e.2 (by simp) (some ℓ) tagWeighted elig
            have hweights : ∀ z : (Slice × Tags) × Acts,
                (jointWeighted.prod actLaw).w z =
                  ((FinProb.prod ps tagWeighted).prod actLaw).w z := by
              intro z
              rcases z with ⟨u, A⟩
              change jointWeighted.w u * actLaw.w A =
                (ps.w u.1 * tagWeighted.w u.2) * actLaw.w A
              rw [hweight u]
              simp [FinProb.prod]
            have hprobEps :
                (FinProb.prod jointWeighted actTie).pr
                  (fun z => Pick (z.1.1, z.1.2) z.2.1 z.2.2) ≤ Real.exp (-(D.n : ℝ) ^ c) := by
              calc
                (FinProb.prod jointWeighted actTie).pr
                  (fun z => Pick (z.1.1, z.1.2) z.2.1 z.2.2) =
                      ((FinProb.prod jointWeighted actLaw).prod tieLaw).pr
                        (fun z => Pick z.1.1 z.1.2 z.2) := by
                          simpa [actTie] using (prod_pr_assoc jointWeighted actLaw tieLaw
                            (fun u A τ => Pick (u.1, u.2) A τ))
                _ ≤ ((FinProb.prod jointWeighted actLaw).prod tieLaw).pr
                      (fun z => HeightEvent z.1.1 z.1.2) := by
                        apply pr_mono
                        intro z hS
                        exact hlocToHeight z.1.1 z.1.2 z.2 hS hℓpos
                _ = (FinProb.prod jointWeighted actLaw).pr
                      (fun z => HeightEvent z.1 z.2) :=
                        prod_pr_ignore_right (FinProb.prod jointWeighted actLaw) tieLaw
                          (fun z => HeightEvent z.1 z.2)
                _ = (FinProb.prod (FinProb.prod ps tagWeighted) actLaw).pr
                      (fun z => HeightEvent z.1 z.2) :=
                        pr_congr_weights (FinProb.prod jointWeighted actLaw)
                          (FinProb.prod (FinProb.prod ps tagWeighted) actLaw)
                          hweights (fun z => HeightEvent z.1 z.2)
                _ ≤ Real.exp (-(D.n : ℝ) ^ c) := hheightProb
            simpa [rate, hzero] using hprobEps
        have hinner :
            ps.expect (fun P => (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
              (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) ≤ mass * rate := by
          have hinnerEq :
              ps.expect (fun P => (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
                (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) =
              joint.expect (fun z => w z.2 * actTie.pr (fun aτ => Pick (z.1, z.2) aτ.1 aτ.2)) := by
            calc
              ps.expect (fun P => (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
                (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) =
                  ps.expect (fun P => tagLaw.expect (fun t =>
                    w t * actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2))) := by
                      apply expect_congr
                      intro P
                      have hrawEq (P : Slice) := by
                        let Event : Tags → Acts × Ties → Prop := fun t aτ => Pick (P, t) aτ.1 aτ.2
                        let f : Tags → Acts → Ties → ℝ := fun t A τ => by
                          exact @ite ℝ (Event t (A, τ)) (Classical.propDecidable _) (w t) 0
                        have hpoint (ω : D.TAT) :
                            selectedCenterTerm D Θ e x (fullPos P) ω.1.1
                              (ω.1.2 e.1) (ω.2 e.1) ℓ = f ω.1.1 (ω.1.2 e.1) (ω.2 e.1) := by
                          have hselCompat (t : Tags) (A : Acts) (τ : Ties) :
                              D.sel ((Θ, fullPos P), ((t, fun _ => A), fun _ => τ)) e =
                                p₀.selection Finset.univ ((fullPos P) g) A
                                  (D.elig Θ (fullPos P) t g) τ e.2 := rfl
                          have hcondition :
                              (D.LocalLegal Θ (fullPos P) ω.1.1 e ∧
                                D.sel ((Θ, fullPos P),
                                  ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1)) e =
                                  some ℓ) = Pick (P, ω.1.1) (ω.1.2 e.1) (ω.2 e.1) := by
                            simp only [Pick]
                            rw [hselCompat]
                          dsimp [selectedCenterTerm, f]
                          by_cases hsel : D.LocalLegal Θ (fullPos P) ω.1.1 e ∧
                              D.sel ((Θ, fullPos P),
                                ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1)) e = some ℓ
                          · have hpick := (Iff.of_eq hcondition).mp hsel
                            have hevent : Event ω.1.1 (ω.1.2 e.1, ω.2 e.1) := by
                              simpa [Event] using hpick
                            simp [hsel, hevent, w, g]
                          · have hnpick : ¬ Pick (P, ω.1.1) (ω.1.2 e.1) (ω.2 e.1) := by
                              intro hpick
                              exact hsel ((Iff.of_eq hcondition).mpr hpick)
                            have hnevent : ¬ Event ω.1.1 (ω.1.2 e.1, ω.2 e.1) := by
                              intro hevent
                              apply hnpick
                              simpa [Event] using hevent
                            simp [hsel, hnevent]
                        have hresult :
                            (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
                              (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ) =
                              tagLaw.expect (fun t => w t * actTie.pr (Event t)) := by
                          calc
                            (D.rawTAT Θ).expect (fun ω => selectedCenterTerm D Θ e x
                                (fullPos P) ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ) =
                              (D.rawTAT Θ).expect (fun ω => f ω.1.1 (ω.1.2 e.1) (ω.2 e.1)) :=
                                expect_congr _ _ _ hpoint
                            _ = tagLaw.expect (fun t => actLaw.expect (fun A =>
                                tieLaw.expect (fun τ => f t A τ))) :=
                                  rawTAT_expect_local_slices D Θ g f
                            _ = tagLaw.expect (fun t => w t * actTie.pr (Event t)) := by
                                  apply expect_congr
                                  intro t
                                  letI : ∀ aτ : Acts × Ties, Decidable (Event t aτ) :=
                                    fun aτ => Classical.propDecidable _
                                  calc
                                    actLaw.expect (fun A => tieLaw.expect (fun τ => f t A τ)) =
                                        actTie.expect (fun aτ =>
                                          @ite ℝ (Event t aτ) (Classical.propDecidable _) (w t) 0) := by
                                          exact (prod_expect actLaw tieLaw
                                            (fun A τ => @ite ℝ (Event t (A, τ))
                                              (Classical.propDecidable _) (w t) 0)).symm
                                    _ = w t * actTie.pr (Event t) :=
                                          expect_event_const actTie (Event t) (w t)
                        simpa [Event] using hresult
                      exact hrawEq P
              _ = joint.expect (fun z => w z.2 * actTie.pr
                  (fun aτ => Pick (z.1, z.2) aτ.1 aτ.2)) :=
                    (prod_expect ps tagLaw
                      (fun P t => w t * actTie.pr (fun aτ => Pick (P, t) aτ.1 aτ.2))).symm
          rw [hinnerEq]
          exact weighted_product_expect_pr_bound joint actTie (fun z => w z.2)
            (fun z => hw z.2) mass hJointMean hmassPos
            (fun z aτ => Pick (z.1, z.2) aτ.1 aτ.2) rate hprobFactor
        exact hinner
    let centerTermAverage : D.Pos → ℝ := fun P =>
      (D.rawTAT Θ).expect (fun ω =>
        selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)
    have hzeroIfAbsent (P : D.Pos) (hnot : ¬ P g ℓ) :
        centerTermAverage P = 0 := by
      have hpoint (ω : D.TAT) :
          selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ = 0 := by
        let q : D.Pre := ((Θ, P), ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1))
        by_cases hL : D.LocalLegal Θ P ω.1.1 e
        · by_cases hS : D.sel q e = some ℓ
          · have hlegal : p₀.Legal (P e.1) (D.elig Θ P ω.1.1 e.1)
                (p₀.domBall Finset.univ e.2 p₀.Rlong) := by
              change p₀.Legal (P e.1) (D.elig Θ P ω.1.1 e.1) _ at hL
              exact hL
            have hsel : p₀.selection Finset.univ (P e.1) (ω.1.2 e.1)
                (D.elig Θ P ω.1.1 e.1) (ω.2 e.1) e.2 = some ℓ := by
              simpa [q, Ctx.sel] using hS
            have hpresent := selected_present_of_local_legal Finset.univ (P e.1)
              (ω.1.2 e.1) (D.elig Θ P ω.1.1 e.1) (ω.2 e.1) e.2 ℓ (by simp)
              hlegal hsel
            exact (hnot (by simpa [g] using hpresent)).elim
          · simp [selectedCenterTerm, q, hL, hS]
        · simp [selectedCenterTerm, q, hL]
      calc
        centerTermAverage P = (D.rawTAT Θ).expect (fun ω => 0) := by
          apply expect_congr
          intro ω
          exact hpoint ω
        _ = 0 := expect_const _ 0
    have hcenterTermSplit :
        D.posLaw.expect centerTermAverage = presentMass *
          (FinProb.prod otherLaw ps).expect (fun z =>
            centerTermAverage (reconstructPos D g z.2 z.1)) := by
      have hvanish : D.posLaw.expect centerTermAverage =
          D.posLaw.expect (fun P => if P g ℓ then centerTermAverage P else 0) := by
        apply expect_congr
        intro P
        by_cases hpresent : P g ℓ
        · simp [hpresent]
        · simp [hpresent, hzeroIfAbsent P hpresent]
      calc
        D.posLaw.expect centerTermAverage =
            D.posLaw.expect (fun P => if P g ℓ then centerTermAverage P else 0) := hvanish
        _ = presentMass * (FinProb.prod otherLaw ps).expect (fun z =>
              centerTermAverage (reconstructPos D g z.2 z.1)) := by
                have hsplit := posLaw_forced_split D g ℓ centerTermAverage
                change D.posLaw.expect (fun P => if P g ℓ then centerTermAverage P else 0) =
                  presentMass * (FinProb.prod otherLaw ps).expect (fun z =>
                    centerTermAverage (reconstructPos D g z.2 z.1)) at hsplit
                exact hsplit
    calc
      D.posLaw.expect centerTermAverage = presentMass *
          (FinProb.prod otherLaw ps).expect (fun z =>
            centerTermAverage (reconstructPos D g z.2 z.1)) := hcenterTermSplit
      _ ≤ presentMass * (mass * rate) :=
        mul_le_mul_of_nonneg_left hForcedBound hpresenceNonneg
      _ = presentMass * mass *
          (if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)) := by
            change presentMass * (mass * rate) = presentMass * mass * rate
            ring
  have hzeroOutside (ℓ : D.Loc) (hnot : ℓ ∉
      ((Finset.univ.filter (fun u : CubeVertex p₀.d => hammingDist u e.2 ≤ p₀.r)).product
        (Finset.univ : Finset (Fin (p₀.H + 1))))) :
      D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
        selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) = 0 := by
    have hfar : ¬ hammingDist ℓ.1 e.2 ≤ p₀.r := by
      intro hd
      apply hnot
      simp [hd]
    have hpoint (P : D.Pos) (ω : D.TAT) :
        selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ = 0 := by
      let q : D.Pre := ((Θ, P), ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1))
      by_cases hL : D.LocalLegal Θ P ω.1.1 e
      · by_cases hS : D.sel q e = some ℓ
        · have hlegal : p₀.Legal (P e.1) (D.elig Θ P ω.1.1 e.1)
              (p₀.domBall Finset.univ e.2 p₀.Rlong) := by
            change p₀.Legal (P e.1) (D.elig Θ P ω.1.1 e.1) _ at hL
            exact hL
          have hsel : p₀.selection Finset.univ (P e.1) (ω.1.2 e.1)
              (D.elig Θ P ω.1.1 e.1) (ω.2 e.1) e.2 = some ℓ := by
            simpa [Ctx.sel] using hS
          have hdist := selected_location_within_ball Finset.univ (P e.1)
            (ω.1.2 e.1) (D.elig Θ P ω.1.1 e.1) (ω.2 e.1) e.2 ℓ (by simp)
            hlegal hsel
          exact (hfar hdist).elim
        · simp [selectedCenterTerm, q, hL, hS]
      · simp [selectedCenterTerm, q, hL]
    calc
      D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
          selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) =
        D.posLaw.expect (fun _ => 0) := by
          apply expect_congr
          intro P
          calc
            (D.rawTAT Θ).expect (fun ω =>
                selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ) =
              (D.rawTAT Θ).expect (fun _ => 0) := by
                apply expect_congr
                intro ω
                exact hpoint P ω
            _ = 0 := expect_const _ 0
      _ = 0 := expect_const _ 0
  let Ball : Finset (CubeVertex p₀.d) :=
    Finset.univ.filter (fun u => hammingDist u e.2 ≤ p₀.r)
  let Centers : Finset D.Loc := Ball.product (Finset.univ : Finset (Fin (p₀.H + 1)))
  have htermSum :
      D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
        (if D.LocalLegal Θ P ω.1.1 e then 1 else 0) *
          D.selLoad ((Θ, P), ω) e x)) =
        ∑ ℓ : D.Loc, D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
          selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) := by
    calc
      _ = D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
          ∑ ℓ : D.Loc, selectedCenterTerm D Θ e x P ω.1.1
            (ω.1.2 e.1) (ω.2 e.1) ℓ)) := by
              apply expect_congr
              intro P
              apply expect_congr
              intro ω
              have hload : D.selLoad ((Θ, P), ω) e x =
                  D.selLoad ((Θ, P), ((ω.1.1, fun _ => ω.1.2 e.1), fun _ => ω.2 e.1)) e x := by
                rfl
              rw [hload]
              exact selectedCenterTerm_sum D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1)
      _ = D.posLaw.expect (fun P => ∑ ℓ : D.Loc,
            (D.rawTAT Θ).expect (fun ω =>
              selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) := by
              apply expect_congr
              intro P
              exact expect_sum (D.rawTAT Θ) (fun ω ℓ =>
                selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)
      _ = ∑ ℓ : D.Loc, D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
            selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) :=
            expect_sum D.posLaw (fun P ℓ => (D.rawTAT Θ).expect (fun ω =>
              selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ))
  have hsumBound :
      (∑ ℓ : D.Loc, D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
        selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ))) ≤
        ∑ ℓ ∈ Centers, presentMass * mass *
          (if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)) := by
    calc
      (∑ ℓ : D.Loc, D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
        selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ))) =
          ∑ ℓ ∈ Centers, D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
            selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) := by
              symm
              apply Finset.sum_subset (Finset.subset_univ Centers)
              intro ℓ hℓ hnot
              exact hzeroOutside ℓ hnot
      _ ≤ ∑ ℓ ∈ Centers, presentMass * mass *
            (if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)) :=
            Finset.sum_le_sum fun ℓ hℓ => hTermBound ℓ
  have hlevelSum :
      ∑ j : Fin (p₀.H + 1),
        (if j.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)) =
        3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c) := by
    rw [Fin.sum_univ_succ]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcenterSum :
      (∑ ℓ ∈ Centers, presentMass * mass *
        (if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c))) =
        presentMass * mass * ((Ball.card : ℝ) *
          (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) := by
    rw [show Centers = Ball.product (Finset.univ : Finset (Fin (p₀.H + 1))) by rfl]
    change (∑ z ∈ Ball ×ˢ (Finset.univ : Finset (Fin (p₀.H + 1))),
      presentMass * mass *
        (if z.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c))) = _
    rw [Finset.sum_product]
    calc
      (∑ u ∈ Ball, ∑ j ∈ (Finset.univ : Finset (Fin (p₀.H + 1))),
          presentMass * mass *
            (if j.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c))) =
        ∑ u ∈ Ball, presentMass * mass *
          (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c)) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [← Finset.mul_sum, hlevelSum]
      _ = presentMass * mass * ((Ball.card : ℝ) *
            (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) := by
              simp [Finset.sum_const, nsmul_eq_mul]
              ring
  have hBallCard : (Ball.card : ℝ) = (p₀.V : ℝ) := by
    dsimp [Ball, p₀]
    rw [loadHammingBallCard]
    rfl
  have hrateTotal :
      presentMass * mass * ((Ball.card : ℝ) *
          (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) ≤ 4 * mass := by
    rw [hBallCard]
    have hqV : presentMass * (p₀.V : ℝ) ≤ p₀.lam := by
      have := mul_le_mul_of_nonneg_right hpresenceLe hVpos.le
      have hdiv : (p₀.lam / (p₀.V : ℝ)) * p₀.V = p₀.lam := by
        field_simp [ne_of_gt hVpos]
      nlinarith
    have hcoeff : p₀.lam *
        (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c)) ≤ 4 := by
      have hfirst : p₀.lam * (3 / p₀.lam) = 3 := by field_simp [ne_of_gt hLamPos]
      nlinarith [hHeightTail]
    calc
      presentMass * mass * ((p₀.V : ℝ) *
          (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) =
        mass * (presentMass * (p₀.V : ℝ) *
          (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) := by ring
      _ ≤ mass * (p₀.lam *
          (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hqV (by positivity)) hmassNonneg
      _ ≤ mass * 4 := mul_le_mul_of_nonneg_left hcoeff hmassNonneg
      _ = 4 * mass := by ring
  have hfinal :
      D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
        (if D.LocalLegal Θ P ω.1.1 e then 1 else 0) * D.selLoad ((Θ, P), ω) e x)) ≤
        D.Bcomp Θ g x := by
    calc
      _ = ∑ ℓ : D.Loc, D.posLaw.expect (fun P => (D.rawTAT Θ).expect (fun ω =>
            selectedCenterTerm D Θ e x P ω.1.1 (ω.1.2 e.1) (ω.2 e.1) ℓ)) := htermSum
      _ ≤ ∑ ℓ ∈ Centers, presentMass * mass *
            (if ℓ.2.val = 0 then 3 / p₀.lam else Real.exp (-(D.n : ℝ) ^ c)) := hsumBound
      _ = presentMass * mass * ((Ball.card : ℝ) *
            (3 / p₀.lam + (p₀.H : ℝ) * Real.exp (-(D.n : ℝ) ^ c))) := hcenterSum
      _ ≤ 4 * mass := hrateTotal
      _ ≤ D.Bcomp Θ g x := by nlinarith [hmassBound]
  simpa [Ctx.SelectMean, g] using hfinal

private def centerRow {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (Θ : D.Hist)
    (a : EvenRole D.n) (x : Fin D.N) (z : D.Pos × D.TAT) : ℝ :=
  (if D.LocalLegal Θ z.1 z.2.1.1 (cellOf η₀ a.1) then 1 else 0) *
    D.selLoad ((Θ, z.1), z.2) (cellOf η₀ a.1) x

private def centerSupport {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (Θ : D.Hist)
    (z : D.Pos × D.TAT) : Prop :=
  ∀ g ℓ, 0 < (D.tilt Θ g).w (z.2.1.1 g ℓ)

private def centerSucc {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h) (Θ : D.Hist) :
    Finset (D.Pos × D.TAT) :=
  Finset.univ.filter fun z => D.SelOK ((Θ, z.1), z.2) ∧ centerSupport D Θ z

set_option maxHeartbeats 5000000 in
private theorem center_tail_scattered_at {η₀ γ β p K c : ℝ} {h : ℕ}
    (D : Ctx η₀ β p h) (X Y R : Finset (Fin D.N)) (hStd : Std D γ K X Y R)
    (hGF : GridFacts η₀ D.n) (Θ : D.Hist) (hgood : ∀ g, ¬ D.HBad Θ g)
    (hcomp : D.CompOK (8 * (40 * K + 1)) Θ) (hc : 0 < c) (hγ₁ : γ < 1)
    (hK : 0 < K)
    (hres : fRes η₀ D.n (2 * rH D.n + 8 * HH η₀ D.n + 4) ≤ Real.exp (-c * D.n))
    (hcap : (D.n : ℝ) * Real.exp (-c * D.n) * centerAnchorCap η₀ γ D ≤ 1)
    (hSM : D.SelectMean) (hSC : D.SelConseq)
    (hjoint : ∀ (x : Fin D.N) (m : ℕ), m ≤ D.n → ∀ s : Fin m → EvenRole D.n,
      (∀ i j : Fin m, j < i → s i ∉ evenResNear η₀
        (2 * rH D.n + 8 * HH η₀ D.n + 4) (s j)) →
      ∑ z ∈ centerSucc D Θ,
        (FinProb.prod D.posLaw (D.rawTAT Θ)).w z * ∏ i, centerRow D Θ (s i) x z ≤
          (1 : ℝ) ^ m * ∏ i, D.Bcomp Θ (keyOf η₀ (s i).1) x) :
    (FinProb.bind D.posLaw fun _ => D.rawTAT Θ).pr
        (fun z => D.SelOK ((Θ, z.1), z.2) ∧
          ¬ D.LoadOK (4 * (8 * (40 * K + 1) + 1)) ((Θ, z.1), z.2)) ≤
      (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  classical
  let U := EvenRole D.n
  let P := FinProb.prod D.posLaw (D.rawTAT Θ)
  let succ := centerSucc D Θ
  let Z : U → Fin D.N → (D.Pos × D.TAT) → ℝ := fun a x z => centerRow D Θ a x z
  let d : U → Fin D.N → ℝ := fun a x => D.Bcomp Θ (keyOf η₀ a.1) x
  have hcard : 0 < Fintype.card U := by rw [hGF.even_card]; positivity
  letI : Nonempty U := Fintype.card_pos_iff.mp hcard
  have hU : 0 < (Fintype.card U : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hZ0 : ∀ a x z, 0 ≤ Z a x z := by
    intro a x z
    dsimp [Z, centerRow]
    apply mul_nonneg (ind_nonneg _)
    unfold Ctx.selLoad
    cases hsel : D.selTag ((Θ, z.1), z.2) (cellOf η₀ a.1) <;> simp [hsel]
    exact mul_nonneg (by positivity) ((D.anchorU Θ _ _).nonneg x)
  have hZL : ∀ a x z, z ∈ succ → Z a x z ≤ centerAnchorCap η₀ γ D := by
    intro a x z hz
    have hs : D.SelOK ((Θ, z.1), z.2) := (Finset.mem_filter.mp hz).2.1
    have htagSupport : centerSupport D Θ z := (Finset.mem_filter.mp hz).2.2
    have hcon := hSC ((Θ, z.1), z.2) hs
    let e : D.CellT := cellOf η₀ a.1
    have hlegal : D.LocalLegal Θ z.1 z.2.1.1 e := (hcon.2 e).2.2.2
    have hsome : (D.sel ((Θ, z.1), z.2) e).isSome := hcon.1 e
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
    have hselTag : D.selTag ((Θ, z.1), z.2) e = some (z.2.1.1 e.1 i) := by
      simp [Ctx.selTag, hi]
    have htag : 0 < (D.tilt Θ e.1).w (z.2.1.1 e.1 i) := htagSupport e.1 i
    have hcap' := anchorU_cap_of_tag_support D X Y R hStd Θ hgood
      (lt_of_lt_of_le (by norm_num) hGF.pos.1) e x (z.2.1.1 e.1 i) htag
    have hload : D.selLoad ((Θ, z.1), z.2) e x ≤ centerAnchorCap η₀ γ D := by
      simpa [Ctx.selLoad, hselTag] using hcap'
    simpa [Z, centerRow, e, hlegal] using hload
  have hself : ∀ a : U, a ∈ evenResNear η₀
      (2 * rH D.n + 8 * HH η₀ D.n + 4) a := by
    intro a
    simp [evenResNear]
  have hf : 0 ≤ fRes η₀ D.n (2 * rH D.n + 8 * HH η₀ D.n + 4) := by
    unfold fRes
    positivity
  have hnear : ∀ a : U,
      ((evenResNear η₀ (2 * rH D.n + 8 * HH η₀ D.n + 4) a).card : ℝ) ≤
        fRes η₀ D.n (2 * rH D.n + 8 * HH η₀ D.n + 4) * Fintype.card U :=
    hGF.res_near _
  have hD0 : 0 ≤ 8 * (40 * K + 1) := by positivity
  have hd : ∀ a x, 0 ≤ d a x := by
    intro a x
    exact bcomp_nonneg D Θ (keyOf η₀ a.1) x
  have hmean : ∀ x,
      (Fintype.card U : ℝ)⁻¹ * ∑ a, d a x ≤ 8 * (40 * K + 1) := by
    intro x
    simpa [d, U, Ctx.CompOK] using hcomp x
  have hsmall : (D.n : ℝ) * fRes η₀ D.n
      (2 * rH D.n + 8 * HH η₀ D.n + 4) * centerAnchorCap η₀ γ D ≤ 1 := by
    have hnR : 0 < (D.n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hGF.pos.1)
    have hdeltaPow : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
    have hdelta : D.Δ < 1 := by
      unfold Ctx.Δ
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hdeltaPow)
    have hcap0 : 0 ≤ centerAnchorCap η₀ γ D := by
      unfold centerAnchorCap
      exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hdelta.le)
    calc
      _ ≤ (D.n : ℝ) * Real.exp (-c * D.n) * centerAnchorCap η₀ γ D := by
        apply mul_le_mul_of_nonneg_right _ hcap0
        exact mul_le_mul_of_nonneg_left hres hnR.le
      _ ≤ 1 := hcap
  have hlabels : (Fintype.card (Fin D.N) : ℝ) ≤ (D.n : ℝ) * 2 ^ D.n := by
    rw [Fintype.card_fin]
    exact_mod_cast hStd.size.2
  have htail := HypercubeRamsey.scatteredMoments_union_labels P succ Z hZ0
    (centerAnchorCap η₀ γ D) (by
      have hnR : 0 < (D.n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hGF.pos.1)
      have hdeltaPow : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
      have hdelta : D.Δ < 1 := by
        unfold Ctx.Δ
        exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hdeltaPow)
      unfold centerAnchorCap
      exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hdelta.le)) hZL
    (evenResNear η₀ (2 * rH D.n + 8 * HH η₀ D.n + 4)) hself
    (fRes η₀ D.n (2 * rH D.n + 8 * HH η₀ D.n + 4)) hf hnear D.n
    (lt_of_lt_of_le (by norm_num) hGF.pos.1) 1 (8 * (40 * K + 1))
    (by norm_num) hD0 d hd hmean (by
      intro x m hm s hsep
      simpa [P, Z, d] using hjoint x m hm s hsep) hsmall hlabels
  have hthreshold : 4 * (1 : ℝ) * (8 * (40 * K + 1) + 1) =
      4 * (8 * (40 * K + 1) + 1) := by ring
  have htailPr : P.pr (fun z => z ∈ succ ∧ ∃ x,
      4 * (8 * (40 * K + 1) + 1) < (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z) ≤
        (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
    classical
    let E : D.Pos × D.TAT → Prop := fun z => z ∈ succ ∧ ∃ x,
      4 * (8 * (40 * K + 1) + 1) < (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z
    have hprsum : P.pr E =
        ∑ z, if z ∈ succ ∧ ∃ x, 4 * (8 * (40 * K + 1) + 1) <
          (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z then P.w z else 0 := by
      unfold FinProb.pr E
      apply Finset.sum_congr rfl
      intro z hz
      by_cases h : z ∈ succ ∧ ∃ x, 4 * (8 * (40 * K + 1) + 1) <
          (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z <;> simp [h]
    calc
      P.pr E = _ := hprsum
      _ ≤ (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
        simpa [hthreshold] using htail
  have hsupportOne : P.pr (centerSupport D Θ) = 1 := by
    change (FinProb.prod D.posLaw (D.rawTAT Θ)).pr
      (fun z => ∀ g ℓ, 0 < (D.tilt Θ g).w (z.2.1.1 g ℓ)) = 1
    exact posTAT_tagSupport_pr_one D Θ
  have hsupportZero : P.pr (fun z => ¬ centerSupport D Θ z) = 0 := by
    have h := pr_compl P (centerSupport D Θ)
    linarith
  have htargetBelowSupport : P.pr (fun z =>
      D.SelOK ((Θ, z.1), z.2) ∧
        ¬ D.LoadOK (4 * (8 * (40 * K + 1) + 1)) ((Θ, z.1), z.2)) ≤
      P.pr (fun z => centerSupport D Θ z ∧
        D.SelOK ((Θ, z.1), z.2) ∧
          ¬ D.LoadOK (4 * (8 * (40 * K + 1) + 1)) ((Θ, z.1), z.2)) := by
    exact pr_le_on_support P (centerSupport D Θ) _ hsupportZero
  have hsupportToTail : ∀ z, centerSupport D Θ z →
      D.SelOK ((Θ, z.1), z.2) →
      ¬ D.LoadOK (4 * (8 * (40 * K + 1) + 1)) ((Θ, z.1), z.2) →
      z ∈ succ ∧ ∃ x, 4 * (8 * (40 * K + 1) + 1) <
        (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z := by
    intro z hsupp hsel hnotload
    have hcon := hSC ((Θ, z.1), z.2) hsel
    have hrowEq : ∀ a x, Z a x z = D.selLoad ((Θ, z.1), z.2)
        (cellOf η₀ a.1) x := by
      intro a x
      have hl : D.LocalLegal Θ z.1 z.2.1.1 (cellOf η₀ a.1) := (hcon.2 (cellOf η₀ a.1)).2.2.2
      simp [Z, centerRow, hl]
    have hsucc : z ∈ succ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hsel, hsupp⟩⟩
    have hnot : ¬ ∀ x, (Fintype.card U : ℝ)⁻¹ *
        ∑ a : U, D.selLoad ((Θ, z.1), z.2) (cellOf η₀ a.1) x ≤
          4 * (8 * (40 * K + 1) + 1) := by
      simpa [Ctx.LoadOK] using hnotload
    obtain ⟨x, hx⟩ := not_forall.mp hnot
    have hx' : 4 * (8 * (40 * K + 1) + 1) <
        (Fintype.card U : ℝ)⁻¹ * ∑ a : U,
          D.selLoad ((Θ, z.1), z.2) (cellOf η₀ a.1) x := by
      exact lt_of_not_ge hx
    refine ⟨hsucc, x, ?_⟩
    simpa [hrowEq] using hx'
  have htailBound := pr_mono P
    (fun z => centerSupport D Θ z ∧ D.SelOK ((Θ, z.1), z.2) ∧
      ¬ D.LoadOK (4 * (8 * (40 * K + 1) + 1)) ((Θ, z.1), z.2))
    (fun z => z ∈ succ ∧ ∃ x, 4 * (8 * (40 * K + 1) + 1) <
      (Fintype.card U : ℝ)⁻¹ * ∑ a, Z a x z)
    (by intro z hz; exact hsupportToTail z hz.1 hz.2.1 hz.2.2)
  have hbound := htargetBelowSupport.trans (htailBound.trans htailPr)
  change (FinProb.prod D.posLaw (D.rawTAT Θ)).pr _ ≤ _ at hbound
  simpa [P, FinProb.bind, FinProb.prod] using hbound

end HypercubeRamsey.S08.Lane_q_s08_load

end
