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

end HypercubeRamsey.S08.Lane_q_s08_load

end
