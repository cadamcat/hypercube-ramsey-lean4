import HypercubeRamsey.S03.Clock.Leaves_p_clock_r2
import HypercubeRamsey.S08.L81.PosteriorNodes

/-!
Private helpers for lane q-s08-load.
-/

noncomputable section

namespace HypercubeRamsey.S08.Lane_q_s08_load

open Classical
open Filter
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
