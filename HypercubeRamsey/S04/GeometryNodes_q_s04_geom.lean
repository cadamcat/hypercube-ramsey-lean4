import HypercubeRamsey.S04.CoreLemmas

namespace HypercubeRamsey.Lane_q_s04_geom

open HypercubeRamsey.S04 OAI.HypercubeRamsey
open scoped BigOperators

/-- Marginalizing an unused second coordinate preserves event probability. -/
theorem pr_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) :
    (FinProb.prod P Q).pr (fun x => A x.1) = P.pr A := by
  classical
  simp only [FinProb.pr, FinProb.prod, Fintype.sum_prod_type]
  have hinner (a : α) :
      (∑ b : β, if A a then P.w a * Q.w b else 0) = if A a then P.w a else 0 := by
    by_cases hA : A a
    · simp [hA, ← Finset.mul_sum, Q.sum_eq_one]
    · simp [hA]
  apply Finset.sum_congr rfl
  intro a _
  exact hinner a

/-- A finite product of events on pairwise disjoint coordinate sets has product probability. -/
private theorem pi_expect_prod_indep {ι α : Type*} {Ω : ι → Type*}
    [Fintype ι] [DecidableEq ι] [∀ i, Fintype (Ω i)] [DecidableEq α]
    (P : ∀ i, FinProb (Ω i)) (I : Finset α)
    (f : α → (∀ i, Ω i) → ℝ) (S : α → Finset ι)
    (hdep : ∀ a, FinProb.DependsOn (f a) (S a))
    (hdisj : ∀ a b, a ≠ b → Disjoint (S a) (S b)) :
    (FinProb.pi P).expect (fun ω => ∏ a ∈ I, f a ω) =
      ∏ a ∈ I, (FinProb.pi P).expect (f a) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using FinProb.expect_const (FinProb.pi P) 1
  | @insert a I ha ih =>
      let U : Finset ι := I.biUnion S
      let g : (∀ i, Ω i) → ℝ := fun ω => ∏ b ∈ I, f b ω
      have hdepG : FinProb.DependsOn g U := by
        intro ω ω' hagree
        dsimp [g]
        apply Finset.prod_congr rfl
        intro b hb
        apply hdep b
        intro i hi
        exact hagree i (Finset.mem_biUnion.mpr ⟨b, hb, hi⟩)
      have hdisjAU : Disjoint (S a) U := by
        apply Finset.disjoint_left.mpr
        intro i hiS hiU
        rcases Finset.mem_biUnion.mp hiU with ⟨b, hb, hiB⟩
        have hab : a ≠ b := by
          intro hab
          subst b
          exact ha hb
        exact (Finset.disjoint_left.mp (hdisj a b hab)) hiS hiB
      calc
        (FinProb.pi P).expect (fun ω => ∏ b ∈ insert a I, f b ω) =
            (FinProb.pi P).expect (fun ω => f a ω * g ω) := by
              apply congrArg
              funext ω
              simp [g, Finset.prod_insert, ha]
        _ = (FinProb.pi P).expect (f a) * (FinProb.pi P).expect g :=
          FinProb.pi_expect_mul_of_disjoint P (f a) g (S a) U (hdep a) hdepG hdisjAU
        _ = (FinProb.pi P).expect (f a) * ∏ b ∈ I, (FinProb.pi P).expect (f b) := by
          rw [ih]
        _ = ∏ b ∈ insert a I, (FinProb.pi P).expect (f b) := by
          simp [Finset.prod_insert, ha]

/-- Probability of a finite union is at most the sum of its event probabilities. -/
private theorem pr_exists_finset_le_sum {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (P : FinProb Ω) (I : Finset α) (E : α → Ω → Prop) :
    P.pr (fun ω => ∃ i ∈ I, E i ω) ≤ ∑ i ∈ I, P.pr (E i) := by
  classical
  letI : ∀ ω, Decidable (∃ i ∈ I, E i ω) := fun _ => Classical.propDecidable _
  letI : ∀ i, ∀ ω, Decidable (E i ω) := fun _ _ => Classical.propDecidable _
  unfold FinProb.pr
  calc
    (∑ ω, if ∃ i ∈ I, E i ω then P.w ω else 0) ≤
        ∑ ω, ∑ i ∈ I, if E i ω then P.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases he : ∃ i ∈ I, E i ω
      · obtain ⟨i, hi, hE⟩ := he
        have hsingle : P.w ω ≤ ∑ i ∈ I, if E i ω then P.w ω else 0 := by
          let f : α → ℝ := fun j => if E j ω then P.w ω else 0
          have hf : ∀ j ∈ I, 0 ≤ f j := by
            intro j hj
            by_cases h : E j ω <;> simp [f, h, P.nonneg ω]
          calc
            P.w ω = f i := by simp [f, hE]
            _ ≤ ∑ j ∈ I, f j := Finset.single_le_sum hf hi
            _ = ∑ j ∈ I, if E j ω then P.w ω else 0 := by rfl
        rw [if_pos (show ∃ j ∈ I, E j ω from ⟨i, hi, hE⟩)]
        exact hsingle
      · have hnonneg : 0 ≤ ∑ i ∈ I, if E i ω then P.w ω else 0 := by
          apply Finset.sum_nonneg
          intro i hi
          by_cases h : E i ω <;> simp [h, P.nonneg ω]
        rw [if_neg he]
        exact hnonneg
    _ = ∑ i ∈ I, P.pr (E i) := by
      rw [Finset.sum_comm]
      simp [FinProb.pr]

/-- Integrating an event against a bind law. -/
private theorem bind_pr_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (K : α → FinProb β) (E : α → β → Prop) :
    (FinProb.bind P K).pr (fun ab => E ab.1 ab.2) =
      ∑ a, P.w a * (K a).pr (E a) := by
  classical
  unfold FinProb.pr FinProb.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b, if E a b then P.w a * (K a).w b else 0) =
        ∑ b, P.w a * (if E a b then (K a).w b else 0) := by
          apply Finset.sum_congr rfl
          intro b hb
          by_cases h : E a b <;> simp [h]
    _ = P.w a * ∑ b, if E a b then (K a).w b else 0 := by rw [Finset.mul_sum]
    _ = P.w a * (K a).pr (E a) := by rfl

/-- Integrating an event against a product law. -/
private theorem prod_pr_eq {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (E : α → β → Prop) :
    (FinProb.prod P Q).pr (fun ab => E ab.1 ab.2) =
      ∑ a, P.w a * Q.pr (E a) := by
  simpa [FinProb.prod, FinProb.bind] using bind_pr_eq P (fun _ => Q) E

/-- The expectation of an indicator is its event probability. -/
private theorem expect_indicator_eq_pr {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (E : Ω → Prop) [DecidablePred E] :
    P.expect (fun ω => if E ω then 1 else 0) = P.pr E := by
  classical
  letI : ∀ ω, Decidable (E ω) := fun _ => Classical.propDecidable _
  unfold FinProb.expect FinProb.pr
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : E ω <;> simp [h]

/-- Invalidity of a fixed candidate depends only on tuple coordinates whose center lies in that candidate. -/
private theorem valid_indicator_depends {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n)
    (D : Finset (Loc β γ n))
    [∀ W : Tuples β γ n N, Decidable (Valid M tag u ((xm, ym), W) D)] :
    FinProb.DependsOn
      (fun W : Tuples β γ n N =>
        if ¬ Valid M tag u ((xm, ym), W) D then (1 : ℝ) else 0)
      (D.product (Finset.univ : Finset (Key β γ n))) := by
  classical
  intro W W' hagree
  have htuple (c : Loc β γ n) (hc : c ∈ D) (κ : Key β γ n) :
      W (c, κ) = W' (c, κ) := by
    exact hagree (c, κ) (Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩)
  have hAll :
      HitsAll E G W D (Zset β γ u) = HitsAll E G W' D (Zset β γ u) := by
    funext y
    apply propext
    simp only [HitsAll]
    constructor
    · intro h c hc κ hκ k
      simpa [htuple c hc κ] using h c hc κ hκ k
    · intro h c hc κ hκ k
      simpa [htuple c hc κ] using h c hc κ hκ k
  have hBut (c₀ : Loc β γ n) (κ₀ : Key β γ n) :
      HitsBut E G W D (Zset β γ u) c₀ κ₀ =
        HitsBut E G W' D (Zset β γ u) c₀ κ₀ := by
    funext y
    apply propext
    simp only [HitsBut]
    constructor
    · intro h c hc κ hne k
      simpa [htuple c hc κ] using h c hc κ hne k
    · intro h c hc κ hne k
      simpa [htuple c hc κ] using h c hc κ hne k
  have hvalid :
      Valid M tag u ((xm, ym), W) D ↔ Valid M tag u ((xm, ym), W') D := by
    constructor
    · intro h
      exact ⟨h.card_pos, h.card_le, by simpa [aym, aW, hAll] using h.mass,
        by simpa [aym, aW, hAll, hBut] using h.ratio⟩
    · intro h
      exact ⟨h.card_pos, h.card_le, by simpa [aym, aW, hAll] using h.mass,
        by simpa [aym, aW, hAll, hBut] using h.ratio⟩
  by_cases h : Valid M tag u ((xm, ym), W) D
  · have h' := hvalid.mp h
    simp [h, h']
  · have h' : ¬ Valid M tag u ((xm, ym), W') D := fun h' => h (hvalid.mpr h')
    simp [h, h']

/-- Invalidity events for pairwise disjoint candidates are independent under the tuple product law. -/
private theorem tuple_all_invalid_prob_bound {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (hValid : ValidProb M tag) (xm : XMasks M tag) (ym : YMasks M tag)
    (u : OddRole n) (F : Finset (Finset (Loc β γ n)))
    (hsize : ∀ D ∈ F, 1 ≤ D.card ∧ D.card ≤ setBd β γ n)
    (hdisj : ∀ D ∈ F, ∀ D' ∈ F, D ≠ D' → Disjoint D D') :
    (tupleLaw M tag xm).pr
      (fun W => ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D) ≤
      (Real.exp (-((n : ℝ) ^ (omega4 β γ / 5)))) ^ F.card := by
  classical
  let q : ℝ := Real.exp (-((n : ℝ) ^ (omega4 β γ / 5)))
  let ind : Finset (Loc β γ n) → Tuples β γ n N → ℝ := fun D W =>
    if ¬ Valid M tag u ((xm, ym), W) D then 1 else 0
  let scope : Finset (Loc β γ n) → Finset (Loc β γ n × Key β γ n) := fun D =>
    if D ∈ F then D.product (Finset.univ : Finset (Key β γ n)) else ∅
  let ind' : Finset (Loc β γ n) → Tuples β γ n N → ℝ := fun D W =>
    if D ∈ F then ind D W else 1
  let P : ∀ ck : Loc β γ n × Key β γ n,
      FinProb (Fin (tupLen β γ n) → Fin N) :=
    fun ck => FinProb.pi fun _ : Fin (tupLen β γ n) => maskLaw (xm ck)
  have hdep : ∀ D, FinProb.DependsOn (ind' D) (scope D) := by
    intro D
    by_cases hD : D ∈ F
    · simpa [ind', scope, hD, ind] using valid_indicator_depends M tag xm ym u D
    · intro W W' hagree
      simp [ind', hD]
  have hscope : ∀ D D', D ≠ D' → Disjoint (scope D) (scope D') := by
    intro D D' hne
    by_cases hD : D ∈ F
    · by_cases hD' : D' ∈ F
      · simp only [scope, if_pos hD, if_pos hD']
        apply Finset.disjoint_left.mpr
        intro ck hck hck'
        rcases Finset.mem_product.mp hck with ⟨hc, hκ⟩
        rcases Finset.mem_product.mp hck' with ⟨hc', hκ'⟩
        exact (Finset.disjoint_left.mp (hdisj D hD D' hD' hne)) hc hc'
      · simp [scope, hD, hD']
    · simp [scope, hD]
  have hprobIndicator :
      (tupleLaw M tag xm).pr (fun W => ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D) =
        (tupleLaw M tag xm).expect (fun W => ∏ D ∈ F, ind D W) := by
    classical
    letI : ∀ W : Tuples β γ n N,
        Decidable (∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D) :=
      fun _ => Classical.propDecidable _
    have hpoint (W : Tuples β γ n N) :
        (if ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D then
            (tupleLaw M tag xm).w W else 0) =
          (tupleLaw M tag xm).w W * ∏ D ∈ F, ind D W := by
      by_cases hall : ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D
      · have hprod : (∏ D ∈ F, ind D W) = 1 := by
          apply Finset.prod_eq_one
          intro D hD
          simp [ind, hall D hD]
        rw [if_pos hall, hprod]
        simp
      · rw [if_neg hall]
        obtain ⟨D, hnot⟩ := not_forall.mp hall
        have hD : D ∈ F := by
          by_contra hD
          apply hnot
          intro hmem
          exact (hD hmem).elim
        have hgood : Valid M tag u ((xm, ym), W) D := by
          by_contra hgood
          apply hnot
          intro _hmem
          exact hgood
        have hz : ind D W = 0 := by simp [ind, hgood]
        have hprod : (∏ D ∈ F, ind D W) = 0 := Finset.prod_eq_zero hD hz
        rw [hprod]
        simp
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro W hW
    exact hpoint W
  have hfactor :
      (tupleLaw M tag xm).expect (fun W => ∏ D ∈ F, ind D W) =
        ∏ D ∈ F, (tupleLaw M tag xm).expect (ind D) := by
    calc
      (tupleLaw M tag xm).expect (fun W => ∏ D ∈ F, ind D W) =
          (tupleLaw M tag xm).expect (fun W => ∏ D ∈ F, ind' D W) := by
        congr 1
        funext W
        apply Finset.prod_congr rfl
        intro D hD
        simp [ind', hD]
      _ = ∏ D ∈ F, (tupleLaw M tag xm).expect (ind' D) := by
        simpa [tupleLaw, P] using pi_expect_prod_indep P F ind' scope hdep hscope
      _ = ∏ D ∈ F, (tupleLaw M tag xm).expect (ind D) := by
        apply Finset.prod_congr rfl
        intro D hD
        simp [ind', hD]
  have hsingle : ∀ D ∈ F, (tupleLaw M tag xm).expect (ind D) ≤ q := by
    intro D hD
    have hEq : (tupleLaw M tag xm).expect (ind D) =
        (tupleLaw M tag xm).pr (fun W => ¬ Valid M tag u ((xm, ym), W) D) := by
      exact expect_indicator_eq_pr _ _
    rw [hEq]
    have h := hValid xm ym u D (hsize D hD).1 (hsize D hD).2
    simpa [q] using h
  have hq : 0 ≤ q := by positivity
  calc
    (tupleLaw M tag xm).pr
        (fun W => ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D) =
        ∏ D ∈ F, (tupleLaw M tag xm).expect (ind D) := by rw [hprobIndicator, hfactor]
    _ ≤ ∏ _D ∈ F, q := by
      apply Finset.prod_le_prod₀
      · intro D hD
        rw [expect_indicator_eq_pr]
        exact pr_nonneg (tupleLaw M tag xm) _
      · intro D hD
        exact hsingle D hD
    _ = q ^ F.card := by simp [Finset.prod_const]

/-- The number of subsets of a finite set with size at most `T` is at most
`(card + 1)^(2T)`. -/
private theorem bounded_powerset_card_le {α : Type*} [DecidableEq α]
    (S : Finset α) (T : ℕ) :
    (S.powerset.filter fun D => 1 ≤ D.card ∧ D.card ≤ T).card ≤ (S.card + 1) ^ (2 * T) := by
  classical
  let C := S.powerset.filter fun D => 1 ≤ D.card ∧ D.card ≤ T
  by_cases hS : S.card = 0
  · have hEmpty : S = ∅ := Finset.card_eq_zero.mp hS
    have hC : C = ∅ := by
      ext D
      constructor
      · intro hD
        have hsub : D ⊆ ∅ := by
          simpa [hEmpty] using Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
        have hDempty : D = ∅ := Finset.subset_empty.mp hsub
        subst D
        simp [C, hEmpty] at hD
      · simp
    change C.card ≤ (S.card + 1) ^ (2 * T)
    rw [hC]
    simp [hS]
  · have hSpos : 0 < S.card := Nat.pos_of_ne_zero hS
    have hfilter : C.filter (fun D => D.card ∈ Finset.range (T + 1)) = C := by
      ext D
      constructor
      · intro hD
        exact (Finset.mem_filter.mp hD).1
      · intro hD
        have hcard : D.card ≤ T := by
          have hC : D ∈ C := hD
          simp only [C, Finset.mem_filter, Finset.mem_powerset] at hC
          exact hC.2.2
        exact Finset.mem_filter.mpr ⟨hD, by simp [Finset.mem_range, hcard]⟩
    have hcardEq : C.card = ∑ k ∈ Finset.range (T + 1), (C.filter fun D => D.card = k).card := by
      have h := Finset.sum_card_fiberwise_eq_card_filter C (Finset.range (T + 1)) Finset.card
      rw [hfilter] at h
      exact h.symm
    have hfiber (k : ℕ) (hk : k ∈ Finset.range (T + 1)) :
        (C.filter fun D => D.card = k).card ≤ (S.card + 1) ^ T := by
      have hsub : (C.filter fun D => D.card = k) ⊆ S.powersetCard k := by
        intro D hD
        have hD' := Finset.mem_filter.mp hD
        have hC : D ∈ C := hD'.1
        simp only [C, Finset.mem_filter, Finset.mem_powerset] at hC
        exact Finset.mem_powersetCard.mpr ⟨hC.1, hD'.2⟩
      calc
        (C.filter fun D => D.card = k).card ≤ (S.powersetCard k).card :=
          Finset.card_le_card hsub
        _ = Nat.choose S.card k := Finset.card_powersetCard k S
        _ ≤ S.card ^ k := Nat.choose_le_pow S.card k
        _ ≤ (S.card + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _ ) k
        _ ≤ (S.card + 1) ^ T := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    have hsum : C.card ≤ (T + 1) * (S.card + 1) ^ T := by
      rw [hcardEq]
      calc
        (∑ k ∈ Finset.range (T + 1), (C.filter fun D => D.card = k).card) ≤
            ∑ _k ∈ Finset.range (T + 1), (S.card + 1) ^ T := by
              apply Finset.sum_le_sum
              intro k hk
              exact hfiber k hk
        _ = (T + 1) * (S.card + 1) ^ T := by simp [Finset.sum_const, nsmul_eq_mul]
    have hnatPow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have hpowpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
          calc
            k + 2 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
            _ ≤ 2 * 2 ^ k := by omega
            _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
    have hTpow : T + 1 ≤ 2 ^ T := hnatPow T
    have hbase : 2 ≤ S.card + 1 := by omega
    calc
      C.card ≤ (T + 1) * (S.card + 1) ^ T := hsum
      _ ≤ 2 ^ T * (S.card + 1) ^ T := Nat.mul_le_mul_right _ hTpow
      _ ≤ (S.card + 1) ^ T * (S.card + 1) ^ T :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hbase T)
      _ = (S.card + 1) ^ (2 * T) := by rw [← Nat.pow_add]; congr 1 <;> omega

noncomputable def cubeNeighborFinset (n : ℕ) (v : CubeVertex n) : Finset (CubeVertex n) := by
  classical
  exact Finset.univ.filter fun w => (cube n).Adj v w

/-- A cube vertex has at most `n` neighbors, by recording its unique flipped coordinate. -/
theorem cube_neighbor_card_le (n : ℕ) (v : CubeVertex n) :
    (cubeNeighborFinset n v).card ≤ n := by
  classical
  let diffs (w : CubeVertex n) : Finset (Fin n) :=
    Finset.univ.filter fun i => v i ≠ w i
  have hcard (w : CubeVertex n) (hw : (cube n).Adj v w) : (diffs w).card = 1 := by
    change (Finset.univ.filter fun i : Fin n => v i ≠ w i).card = 1
    change _ = 1 at hw
    exact hw
  let neigh := {w : CubeVertex n // (cube n).Adj v w}
  let coord (w : neigh) : Fin n :=
    Classical.choose (Finset.card_eq_one.mp (hcard w.1 w.2))
  have hdiff (w : neigh) : diffs w.1 = {coord w} :=
    Classical.choose_spec (Finset.card_eq_one.mp (hcard w.1 w.2))
  have hinj : Function.Injective coord := by
    intro w w' hww'
    apply Subtype.ext
    funext i
    by_cases hi : i = coord w
    · subst i
      have hmem₁ : coord w ∈ diffs w.1 := by rw [hdiff]; simp
      have hmem₂ : coord w ∈ diffs w'.1 := by rw [hdiff, ← hww']; simp
      have hne₁ : v (coord w) ≠ w.1 (coord w) := (Finset.mem_filter.mp hmem₁).2
      have hne₂ : v (coord w) ≠ w'.1 (coord w) := (Finset.mem_filter.mp hmem₂).2
      cases hv : v (coord w) <;> cases h₁ : w.1 (coord w) <;>
        cases h₂ : w'.1 (coord w) <;> simp_all
    · have hi' : i ≠ coord w' := by simpa [hww'] using hi
      have hnot₁ : i ∉ diffs w.1 := by rw [hdiff]; simpa
      have hnot₂ : i ∉ diffs w'.1 := by rw [hdiff]; simpa
      have heq₁ : v i = w.1 i := by
        by_contra hne
        exact hnot₁ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      have heq₂ : v i = w'.1 i := by
        by_contra hne
        exact hnot₂ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact heq₁.symm.trans heq₂
  have hcard' : Fintype.card neigh ≤ Fintype.card (Fin n) :=
    Fintype.card_le_of_injective coord hinj
  have hsub : Fintype.card neigh = (cubeNeighborFinset n v).card := by
    simpa [neigh, cubeNeighborFinset] using
      (Fintype.card_subtype (fun w : CubeVertex n => (cube n).Adj v w))
  simpa [hsub] using hcard'

/-- The odd-role vertices adjacent to a fixed site are among its `n` cube neighbors. -/
noncomputable def oddNeighborRoleFinset {n : ℕ} (v : CubeVertex n) : Finset (OddRole n) := by
  classical
  exact Finset.univ.filter fun u => v ∈ oddAdj u

theorem odd_role_neighbors_card_le {n : ℕ} (v : CubeVertex n) :
    (oddNeighborRoleFinset v).card ≤ n := by
  classical
  let U : Finset (OddRole n) := oddNeighborRoleFinset v
  let V : Finset (CubeVertex n) := U.image Subtype.val
  have himage : V.card = U.card :=
    Finset.card_image_of_injective U Subtype.val_injective
  have hsub : V ⊆ cubeNeighborFinset n v := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨u, hu, rfl⟩
    have hv : v ∈ oddAdj u := (Finset.mem_filter.mp hu).2
    have hadj : (cube n).Adj u.1 v := by simpa [oddAdj] using hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (cube n).adj_comm u.1 v |>.mp hadj⟩
  calc
    U.card = V.card := himage.symm
    _ ≤ (cubeNeighborFinset n v).card := Finset.card_le_card hsub
    _ ≤ n := cube_neighbor_card_le n v

private theorem oddAdj_card_le {n : ℕ} (u : OddRole n) : (oddAdj u).card ≤ n := by
  simpa [oddAdj, cubeNeighborFinset] using cube_neighbor_card_le n u.1

/-- Every marked set is a candidate set in the position pool. -/
theorem marked_candidate {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (P : Pos β γ n) (a : Aux M tag) (u : OddRole n) (j : Fin (topH β γ n))
    {D : Finset (Loc β γ n)} (hD : D ∈ marked M tag P a u j) :
    D ⊆ pool P u j ∧ 1 ≤ D.card ∧ D.card ≤ setBd β γ n := by
  classical
  have hs := greedy_spec ((cands P u j).filter fun D => ¬ Valid M tag u a D).toList
  have hlist : D ∈ ((cands P u j).filter fun D => ¬ Valid M tag u a D).toList := by
    exact hs.1 D (by simpa [marked] using hD)
  have hfilter : D ∈ (cands P u j).filter fun D => ¬ Valid M tag u a D := by
    simpa using hlist
  have hCand := (Finset.mem_filter.mp hfilter).1
  have hCand' := Finset.mem_filter.mp hCand
  exact ⟨Finset.mem_powerset.mp hCand'.1, hCand'.2.1, hCand'.2.2⟩

/-- Every marked set has the prescribed size bound. -/
theorem marked_card_le_setBd {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (P : Pos β γ n) (a : Aux M tag) (u : OddRole n) (j : Fin (topH β γ n))
    {D : Finset (Loc β γ n)} (hD : D ∈ marked M tag P a u j) :
    D.card ≤ setBd β γ n := (marked_candidate M tag P a u j hD).2.2

private theorem marked_invalid {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (P : Pos β γ n) (a : Aux M tag) (u : OddRole n) (j : Fin (topH β γ n))
    {D : Finset (Loc β γ n)} (hD : D ∈ marked M tag P a u j) :
    ¬ Valid M tag u a D := by
  classical
  let L := ((cands P u j).filter fun D => ¬ Valid M tag u a D).toList
  have hs := greedy_spec L
  have hlist : D ∈ L := by simpa [L, marked] using hs.1 D hD
  have hfilter : D ∈ (cands P u j).filter fun D => ¬ Valid M tag u a D := by
    simpa [L] using hlist
  exact (Finset.mem_filter.mp hfilter).2

/-- At one site-level, at most two consecutive height pairs can mark a forbidden ID. -/
private theorem level_pairs_card_le_two {β γ : ℝ} {n : ℕ}
    (l : Fin (topH β γ n + 1)) :
    ((Finset.univ : Finset (Fin (topH β γ n))).filter
      (fun j => j.val = l.val ∨ j.val + 1 = l.val)).card ≤ 2 := by
  classical
  let J := (Finset.univ : Finset (Fin (topH β γ n))).filter
    (fun j => j.val = l.val ∨ j.val + 1 = l.val)
  let f : {j // j ∈ J} → Bool := fun j => if j.1.val = l.val then true else false
  have hf : Function.Injective f := by
    intro j j' h
    have hj := (Finset.mem_filter.mp j.2).2
    have hj' := (Finset.mem_filter.mp j'.2).2
    by_cases h₁ : j.1.val = l.val <;> by_cases h₂ : j'.1.val = l.val
    · apply Subtype.ext
      apply Fin.ext
      exact h₁.trans h₂.symm
    · simp [f, h₁, h₂] at h
    · simp [f, h₁, h₂] at h
    · have hj₁ : j.1.val + 1 = l.val := hj.resolve_left h₁
      have hj₂ : j'.1.val + 1 = l.val := hj'.resolve_left h₂
      apply Subtype.ext
      apply Fin.ext
      omega
  have hc := Fintype.card_le_of_injective f hf
  simpa only [J, Fintype.card_coe, Fintype.card_bool] using hc

/-- At one even site and level, only the marked sets of its odd neighbors at the two
adjacent level pairs can contribute forbidden IDs. -/
theorem forbidden_card_le {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (P : Pos β γ n) (a : Aux M tag) (v : CubeVertex n)
    (l : Fin (topH β γ n + 1))
    (hFam : ∀ u : OddRole n, ∀ j : Fin (topH β γ n),
      (marked M tag P a u j).card < n) :
    (forbidden M tag P a v l).card ≤ 2 * n ^ 2 * setBd β γ n := by
  classical
  let U : Finset (OddRole n) := oddNeighborRoleFinset v
  let J : Finset (Fin (topH β γ n)) :=
    Finset.univ.filter fun j => j.val = l.val ∨ j.val + 1 = l.val
  let W : Finset (Loc β γ n) := U.biUnion fun u =>
    J.biUnion fun j => (marked M tag P a u j).biUnion fun D => D
  have hU : U.card ≤ n := by simpa [U] using odd_role_neighbors_card_le v
  have hJ : J.card ≤ 2 := by simpa [J] using level_pairs_card_le_two l
  have hsub : forbidden M tag P a v l ⊆ W := by
    intro c hc
    have hc' : c ∈ Finset.univ.filter (fun c : Loc β γ n =>
        c.2 = l ∧ ∃ u : OddRole n, v ∈ oddAdj u ∧
          ∃ j, ∃ D ∈ marked M tag P a u j, c ∈ D) := by
      simpa [forbidden] using hc
    rcases (Finset.mem_filter.mp hc').2 with ⟨hl, u, huv, j, D, hD, hcD⟩
    have hu : u ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
    have hCand := marked_candidate M tag P a u j hD
    have hpool : c ∈ pool P u j := hCand.1 hcD
    have hlevel := (Finset.mem_filter.mp hpool).2.2.1
    have hlval : c.2.val = l.val := congrArg Fin.val hl
    have hj : j ∈ J := by
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hlevel with h | h
      · exact Or.inl (h.symm.trans hlval)
      · exact Or.inr (h.symm.trans hlval)
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_biUnion.mpr ⟨j, hj,
      Finset.mem_biUnion.mpr ⟨D, hD, hcD⟩⟩⟩
  have hmarkedUnion (u : OddRole n) (j : Fin (topH β γ n)) :
      ((marked M tag P a u j).biUnion fun D => D).card ≤ n * setBd β γ n := by
    calc
      ((marked M tag P a u j).biUnion fun D => D).card ≤
          ∑ D ∈ marked M tag P a u j, D.card := Finset.card_biUnion_le
      _ ≤ ∑ _D ∈ marked M tag P a u j, setBd β γ n := by
        apply Finset.sum_le_sum
        intro D hD
        exact marked_card_le_setBd M tag P a u j hD
      _ = (marked M tag P a u j).card * setBd β γ n := by simp
      _ ≤ n * setBd β γ n := Nat.mul_le_mul_right _ (Nat.le_of_lt (hFam u j))
  have hW : W.card ≤ 2 * n ^ 2 * setBd β γ n := by
    calc
      W.card ≤ ∑ u ∈ U, (J.biUnion fun j => (marked M tag P a u j).biUnion fun D => D).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ u ∈ U, ∑ j ∈ J, ((marked M tag P a u j).biUnion fun D => D).card := by
        apply Finset.sum_le_sum
        intro u hu
        exact Finset.card_biUnion_le
      _ ≤ ∑ u ∈ U, ∑ j ∈ J, n * setBd β γ n := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro j hj
        exact hmarkedUnion u j
      _ = U.card * J.card * (n * setBd β γ n) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ 2 * n ^ 2 * setBd β γ n := by
        have hUJ : U.card * J.card ≤ n * 2 := Nat.mul_le_mul hU hJ
        calc
          U.card * J.card * (n * setBd β γ n) ≤ n * 2 * (n * setBd β γ n) :=
            Nat.mul_le_mul_right _ hUJ
          _ = 2 * n ^ 2 * setBd β γ n := by ring
  exact (Finset.card_le_card hsub).trans hW

/-- IDs at one level in a site ball are in bijection with the counted cube vertices. -/
theorem rawAt_card_eq_countAt {β γ : ℝ} {n : ℕ}
    (P : Pos β γ n) (v : CubeVertex n) (l : Fin (topH β γ n + 1)) :
    (Finset.univ.filter fun c : Loc β γ n =>
      P c = true ∧ c.2 = l ∧ hammingDist c.1 v ≤ radius β γ n).card = countAt P v l := by
  classical
  let B : Finset (CubeVertex n) := Finset.univ.filter fun u =>
    P (u, l) = true ∧ hammingDist u v ≤ radius β γ n
  let f : CubeVertex n → Loc β γ n := fun u => (u, l)
  have hf : Function.Injective f := by
    intro u u' h
    exact congrArg Prod.fst h
  have himage :
      B.image f = Finset.univ.filter fun c : Loc β γ n =>
        P c = true ∧ c.2 = l ∧ hammingDist c.1 v ≤ radius β γ n := by
    ext c
    constructor
    · intro hc
      rcases Finset.mem_image.mp hc with ⟨u, hu, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨(Finset.mem_filter.mp hu).2.1, rfl, (Finset.mem_filter.mp hu).2.2⟩⟩
    · intro hc
      rcases (Finset.mem_filter.mp hc).2 with ⟨hP, hl, hdist⟩
      refine Finset.mem_image.mpr ⟨c.1, ?_, ?_⟩
      · have heq : c = (c.1, l) := Prod.ext rfl hl
        have hP' : P (c.1, l) = true := by rw [← heq]; exact hP
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hP', hdist⟩⟩
      · exact Prod.ext rfl hl.symm
  calc
    _ = (B.image f).card := by rw [himage]
    _ = B.card := Finset.card_image_of_injective B hf
    _ = countAt P v l := by rfl

/-- With all count balls at most `2λ`, the pool at one odd role and level pair has at most `4 n^11` IDs. -/
private theorem pool_card_le_upper {β γ : ℝ} {n : ℕ}
    (P : Pos β γ n) (u : OddRole n) (j : Fin (topH β γ n))
    (hupper : ∀ v l, (countAt P v l : ℝ) ≤ 2 * lamH n) :
    (pool P u j).card ≤ 4 * n ^ 11 := by
  classical
  let l₀ : Fin (topH β γ n + 1) := ⟨j.val, by omega⟩
  let l₁ : Fin (topH β γ n + 1) := ⟨j.val + 1, by omega⟩
  let Raw : CubeVertex n → Fin (topH β γ n + 1) → Finset (Loc β γ n) := fun v l =>
    Finset.univ.filter fun c =>
      P c = true ∧ c.2 = l ∧ _root_.hammingDist c.1 v ≤ radius β γ n
  let W : Finset (Loc β γ n) := (oddAdj u).biUnion fun v => Raw v l₀ ∪ Raw v l₁
  have hRawCard (v : CubeVertex n) (l : Fin (topH β γ n + 1)) :
      (Raw v l).card = countAt P v l := by
    dsimp [Raw]
    exact rawAt_card_eq_countAt P v l
  have hcountNat (v : CubeVertex n) (l : Fin (topH β γ n + 1)) :
      countAt P v l ≤ 2 * n ^ 10 := by
    have h := hupper v l
    have h' : (countAt P v l : ℝ) ≤ 2 * (n : ℝ) ^ 10 := by simpa [lamH] using h
    exact_mod_cast h'
  have hrawNat (v : CubeVertex n) (l : Fin (topH β γ n + 1)) :
      (Raw v l).card ≤ 2 * n ^ 10 := by rw [hRawCard]; exact hcountNat v l
  have hpoolSub : pool P u j ⊆ W := by
    intro c hc
    change c ∈ (Finset.univ.filter fun c : Loc β γ n =>
      P c = true ∧ (c.2.val = j.val ∨ c.2.val = j.val + 1) ∧
        ∃ v ∈ oddAdj u, _root_.hammingDist c.1 v ≤ radius β γ n) at hc
    rcases (Finset.mem_filter.mp hc).2 with ⟨hP, hlevels, v, hv, hdist⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨v, hv, Finset.mem_union.mpr ?_⟩
    rcases hlevels with hlevel | hlevel
    · left
      change c ∈ Raw v l₀
      simp only [Raw, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hP, Fin.ext hlevel, hdist⟩
    · right
      change c ∈ Raw v l₁
      simp only [Raw, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hP, Fin.ext hlevel, hdist⟩
  have hW : W.card ≤ n * (4 * n ^ 10) := by
    calc
      W.card ≤ ∑ v ∈ oddAdj u, (Raw v l₀ ∪ Raw v l₁).card := Finset.card_biUnion_le
      _ ≤ ∑ v ∈ oddAdj u, ((Raw v l₀).card + (Raw v l₁).card) := by
        apply Finset.sum_le_sum
        intro v hv
        exact Finset.card_union_le _ _
      _ ≤ ∑ _v ∈ oddAdj u, 4 * n ^ 10 := by
        apply Finset.sum_le_sum
        intro v hv
        have h₀ := hrawNat v l₀
        have h₁ := hrawNat v l₁
        omega
      _ = (oddAdj u).card * (4 * n ^ 10) := by simp [Finset.sum_const]
      _ ≤ n * (4 * n ^ 10) := Nat.mul_le_mul_right _ (oddAdj_card_le u)
  calc
    (pool P u j).card ≤ W.card := Finset.card_le_card hpoolSub
    _ ≤ n * (4 * n ^ 10) := hW
    _ = 4 * n ^ 11 := by ring

/-- The fixed binomial layer at radius eleven already dominates the `n^10` position intensity
once the radius has reached eleven and `n` is sufficiently large. -/
theorem hd_count_parameters {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (n : ℕ) (hn : 22 ^ 11 ≤ n) :
    (hd β γ n).r ≤ (hd β γ n).d ∧
      0 < (hd β γ n).V ∧
      lamH n / ((hd β γ n).V : ℝ) ≤ 1 := by
  let p := hd β γ n
  have hn22 : (22 : ℝ) ^ 11 ≤ n := by exact_mod_cast hn
  have hn121 : (121 : ℝ) ≤ n := by
    have hpow : (121 : ℝ) ≤ (22 : ℝ) ^ 11 := by norm_num
    exact hpow.trans hn22
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ (22 : ℝ) ^ 11 := by norm_num
    exact this.trans hn22
  have hωpos := omega4_pos hβ hγ
  have hωlt := omega4_lt hβ hβγ
  have hρ0 : 0 ≤ rhoH β γ := by
    dsimp [rhoH, b0H, bH]
    linarith
  have hρhalf : rhoH β γ < 1 / 2 := by
    dsimp [rhoH, b0H, bH]
    linarith
  have hexpLower : 1 / 2 ≤ 1 - rhoH β γ := by linarith
  have hroot : 11 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have hs := Real.sqrt_le_sqrt hn121
    norm_num at hs ⊢
    exact hs
  have hrpowLower : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) ^ (1 - rhoH β γ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 hexpLower
  have hradiusLowerReal : (11 : ℝ) ≤ (n : ℝ) ^ (1 - rhoH β γ) :=
    hroot.trans hrpowLower
  have hradiusLower : 11 ≤ radius β γ n := by
    unfold radius
    exact Nat.le_floor hradiusLowerReal
  have hterm : 11 ∈ Finset.range (p.r + 1) := by
    simp only [Finset.mem_range]
    dsimp [p, hd]
    omega
  have hchooseV : Nat.choose n 11 ≤ p.V := by
    dsimp [p, HDParams.V, hd]
    apply Finset.single_le_sum
    · intro i hi
      exact Nat.zero_le _
    · simpa [Finset.mem_range] using hterm
  have hchooseLower : (n : ℝ) ^ 10 ≤ (Nat.choose n 11 : ℕ) := by
    have hnumerator : (n : ℝ) / 2 ≤ ((n + 1 - 11 : ℕ) : ℝ) := by
      have hcast : ((n + 1 - 11 : ℕ) : ℝ) = (n : ℝ) + 1 - 11 := by
        rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        norm_num
      rw [hcast]
      linarith
    have hnumPow : (n : ℝ) ^ 10 ≤
        ((n + 1 - 11 : ℕ) : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) := by
      have hfirst : (n : ℝ) ^ 10 ≤ (n : ℝ) ^ 11 / (22 : ℝ) ^ 11 := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < (22 : ℝ) ^ 11)).2
        have hmul := mul_le_mul_of_nonneg_left hn22 (show 0 ≤ (n : ℝ) ^ 10 by positivity)
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hmiddle : (n : ℝ) ^ 11 / (22 : ℝ) ^ 11 =
          ((n : ℝ) / 2) ^ 11 / (11 : ℝ) ^ 11 := by
        field_simp
        norm_num [show (22 : ℝ) = 2 * 11 by norm_num]
      have hfactorial : (Nat.factorial 11 : ℝ) ≤ (11 : ℝ) ^ 11 := by norm_num
      have hsecond : ((n : ℝ) / 2) ^ 11 / (11 : ℝ) ^ 11 ≤
          ((n : ℝ) / 2) ^ 11 / (Nat.factorial 11 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hfactorial
      have hthird : ((n : ℝ) / 2) ^ 11 / (Nat.factorial 11 : ℝ) ≤
          ((n + 1 - 11 : ℕ) : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) :=
        div_le_div_of_nonneg_right (by gcongr) (by positivity)
      exact hfirst.trans_eq hmiddle |>.trans (hsecond.trans hthird)
    have hchooseCast :
        ((n + 1 - 11 : ℕ) : ℝ) ^ 11 / (Nat.factorial 11 : ℝ) ≤ (Nat.choose n 11 : ℝ) := by
      exact Nat.pow_le_choose 11 n
    exact hnumPow.trans hchooseCast
  have hVlower : (n : ℝ) ^ 10 ≤ (p.V : ℝ) := by
    exact hchooseLower.trans (by exact_mod_cast hchooseV)
  have hlam : lamH n = (n : ℝ) ^ 10 := by simp [lamH]
  have hpV : 0 < (p.V : ℝ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
    exact lt_of_lt_of_le (by positivity) hVlower
  constructor
  · change radius β γ n ≤ n
    have hradiusUpper : (n : ℝ) ^ (1 - rhoH β γ) ≤ n := by
      calc
        (n : ℝ) ^ (1 - rhoH β γ) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith [hρ0])
        _ = n := by simp
    have hfloor : ((radius β γ n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact (Nat.floor_le (by positivity)).trans hradiusUpper
    exact_mod_cast hfloor
  · constructor
    · have hpVNat : 0 < p.V := by exact_mod_cast hpV
      change 0 < (hd β γ n).V
      exact hpVNat
    · change lamH n / (p.V : ℝ) ≤ 1
      rw [hlam]
      exact (div_le_one₀ hpV).2 hVlower

/-- A crude explicit bound for the top height scale. -/
private theorem topH_le_pow {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (n : ℕ) (hn : 4 ≤ n) : topH β γ n ≤ n ^ (n + 2) := by
  let R₀ : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ sigmaH β γ⌉₊
  let target : ℕ := ⌈(n : ℝ) ^ (1 - zetaH β γ)⌉₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hωpos := omega4_pos hβ hγ
  have hωlt := omega4_lt hβ hβγ
  have hσ0 : 0 ≤ sigmaH β γ := by
    dsimp [sigmaH, zetaH, b0H, bH]
    linarith
  have hσ1 : sigmaH β γ ≤ 1 := by
    dsimp [sigmaH, zetaH, b0H, bH]
    linarith
  have hζ0 : 0 ≤ zetaH β γ := by
    dsimp [zetaH, b0H, bH]
    linarith
  have hζ1 : zetaH β γ ≤ 1 := by
    dsimp [zetaH, b0H, bH]
    linarith
  have hMceil : ⌈(n : ℝ) ^ sigmaH β γ⌉₊ ≤ n := by
    apply Nat.ceil_le.mpr
    calc
      (n : ℝ) ^ sigmaH β γ ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR hσ1
      _ = n := by simp
  have hM : M ≤ n := by
    dsimp [M]
    exact max_le (by omega) hMceil
  have hM2 : 2 ≤ M := by dsimp [M]; omega
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlogLe : Real.log (n : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < n)
    linarith
  have hlogSq : Real.log (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    (sq_le_sq₀ hlog0 (by positivity)).2 hlogLe
  have hRceil : ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ n ^ 2 := by
    apply Nat.ceil_le.mpr
    simpa [Nat.cast_pow] using hlogSq
  have hR : R₀ ≤ n ^ 2 := by
    dsimp [R₀]
    exact max_le (Nat.one_le_pow 2 n (by omega)) hRceil
  have hR1 : 1 ≤ R₀ := by dsimp [R₀]; omega
  have htargetCeil : target ≤ n := by
    dsimp [target]
    apply Nat.ceil_le.mpr
    calc
      (n : ℝ) ^ (1 - zetaH β γ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hζ0])
      _ = n := by simp
  have htargetPow : target ≤ 2 ^ target := by
    induction target with
    | zero => simp
    | succ k ih =>
      have hkpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      calc
        k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ ih
        _ ≤ 2 * 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
  have htargetM : target ≤ M ^ target * R₀ := by
    calc
      target ≤ 2 ^ target := htargetPow
      _ ≤ M ^ target := Nat.pow_le_pow_left hM2 target
      _ = M ^ target * 1 := by simp
      _ ≤ M ^ target * R₀ := Nat.mul_le_mul_left _ hR1
  have hExists : ∃ i : ℕ, target ≤ M ^ i * R₀ := ⟨target, htargetM⟩
  have hfind : Nat.find hExists ≤ target := Nat.find_min' hExists htargetM
  have htopEq : topH β γ n = M ^ Nat.find hExists * R₀ := by
    dsimp [topH, topScale, R₀, M, target]
  rw [htopEq]
  calc
    M ^ Nat.find hExists * R₀ ≤ n ^ Nat.find hExists * n ^ 2 :=
      Nat.mul_le_mul (by gcongr) hR
    _ ≤ n ^ target * n ^ 2 := by
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hfind)
    _ = n ^ (target + 2) := by rw [Nat.pow_add]
    _ ≤ n ^ (n + 2) := Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right htargetCeil 2)

/-- Conditional on positions and masks, a large marked family has exponentially small tuple probability. -/
private theorem family_tuple_bound {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (hValid : ValidProb M tag) (P : Pos β γ n) (xm : XMasks M tag) (ym : YMasks M tag)
    (hupper : ∀ v l, (countAt P v l : ℝ) ≤ 2 * lamH n)
    (hn60 : 60 ≤ n)
    (hGrowth : 2 * (100 / (omega4 β γ / 60)) ≤
      (n : ℝ) ^ (3 * omega4 β γ / 20)) :
    (tupleLaw M tag xm).pr
      (fun W => ∃ u : OddRole n, ∃ j : Fin (topH β γ n),
        n ≤ (marked M tag P ((xm, ym), W) u j).card) ≤ 1 / 30 := by
  classical
  let T : ℕ := setBd β γ n
  let b : ℝ := omega4 β γ / 30
  let a : ℝ := omega4 β γ / 5
  let ε : ℝ := omega4 β γ / 60
  let δ : ℝ := 3 * omega4 β γ / 20
  let C : ℝ := 100 / ε
  let q : ℝ := Real.exp (-((n : ℝ) ^ a))
  have hωpos := omega4_pos hβ hγ
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnPos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hnR
  have hTle : (T : ℝ) ≤ 4 * (n : ℝ) ^ b := by
    have hceil : (T : ℝ) < 3 * (n : ℝ) ^ b + 1 := by
      simpa [T, setBd, b, bH] using
        (Nat.ceil_lt_add_one (show 0 ≤ 3 * (n : ℝ) ^ (omega4 β γ / 30) by positivity))
    have hpow : 1 ≤ (n : ℝ) ^ b := Real.one_le_rpow hnR hbpos.le
    dsimp [T, b] at hceil ⊢
    linarith
  have hpoolPlus (u : OddRole n) (j : Fin (topH β γ n)) :
      (pool P u j).card + 1 ≤ n ^ 12 := by
    have hpool := pool_card_le_upper P u j hupper
    have hpow : 1 ≤ n ^ 11 := Nat.one_le_pow 11 n (by omega)
    calc
      (pool P u j).card + 1 ≤ 4 * n ^ 11 + 1 := Nat.add_le_add_right hpool 1
      _ ≤ 5 * n ^ 11 := by omega
      _ ≤ n ^ 12 := by
        calc
          5 * n ^ 11 ≤ n * n ^ 11 := Nat.mul_le_mul_right _ (by omega)
          _ = n ^ 12 := by rw [Nat.pow_succ]; ring
  let Cand : OddRole n → Fin (topH β γ n) → Finset (Finset (Loc β γ n)) :=
    fun u j => cands P u j
  let Families : OddRole n → Fin (topH β γ n) → Finset (Finset (Finset (Loc β γ n))) :=
    fun u j => (Cand u j).powersetCard n |>.filter (fun F =>
      ∀ D ∈ F, ∀ D' ∈ F, D ≠ D' → Disjoint D D')
  have hCandBound (u : OddRole n) (j : Fin (topH β γ n)) :
      (Cand u j).card ≤ n ^ (24 * T) := by
    have h₀ := bounded_powerset_card_le (pool P u j) T
    have h₁ : (Cand u j).card ≤ ((pool P u j).card + 1) ^ (2 * T) := by
      simpa [Cand, cands, T] using h₀
    calc
      (Cand u j).card ≤ ((pool P u j).card + 1) ^ (2 * T) := h₁
      _ ≤ (n ^ 12) ^ (2 * T) := Nat.pow_le_pow_left (hpoolPlus u j) (2 * T)
      _ = ((n ^ 12) ^ 2) ^ T := by rw [Nat.pow_mul]
      _ = (n ^ (12 * 2)) ^ T := by rw [(Nat.pow_mul n 12 2).symm]
      _ = n ^ ((12 * 2) * T) := (Nat.pow_mul n (12 * 2) T).symm
      _ = n ^ (24 * T) := by congr 1
  have hFamiliesBound (u : OddRole n) (j : Fin (topH β γ n)) :
      (Families u j).card ≤ n ^ (24 * T * n) := by
    calc
      (Families u j).card ≤ ((Cand u j).powersetCard n).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nat.choose (Cand u j).card n := Finset.card_powersetCard n (Cand u j)
      _ ≤ (Cand u j).card ^ n := Nat.choose_le_pow _ _
      _ ≤ (n ^ (24 * T)) ^ n := Nat.pow_le_pow_left (hCandBound u j) n
      _ = n ^ (24 * T * n) := (Nat.pow_mul n (24 * T) n).symm
  have hMarkedFam (W : Tuples β γ n N) (u : OddRole n) (j : Fin (topH β γ n))
      (hlarge : n ≤ (marked M tag P ((xm, ym), W) u j).card) :
      ∃ F ∈ Families u j, ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D := by
    let A : Aux M tag := ((xm, ym), W)
    let L := ((cands P u j).filter fun D => ¬ Valid M tag u A D).toList
    have hspec := greedy_spec L
    obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq hlarge
    have hFsubCand : F ⊆ Cand u j := by
      intro D hD
      have hMarkD : D ∈ marked M tag P A u j := hFsub hD
      rcases marked_candidate M tag P A u j hMarkD with ⟨hsub, hpos, hsize⟩
      simp only [Cand, cands, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hsub, ⟨hpos, hsize⟩⟩
    have hFdisj : ∀ D ∈ F, ∀ D' ∈ F, D ≠ D' → Disjoint D D' := by
      intro D hD D' hD' hne
      exact hspec.2.1 D (hFsub hD) D' (hFsub hD') hne
    have hFmem : F ∈ Families u j := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨hFsubCand, hFcard⟩, ?_⟩
      intro D hD D' hD' hne
      exact hFdisj D hD D' hD' hne
    refine ⟨F, hFmem, ?_⟩
    intro D hD
    exact marked_invalid M tag P A u j (hFsub hD)
  let EventAt : OddRole n → Fin (topH β γ n) → Tuples β γ n N → Prop :=
    fun u j W => ∃ F ∈ Families u j, ∀ D ∈ F,
      ¬ Valid M tag u ((xm, ym), W) D
  have hEventAt (u : OddRole n) (j : Fin (topH β γ n)) :
      (tupleLaw M tag xm).pr (EventAt u j) ≤
        (n ^ (24 * T * n) : ℕ) * q ^ n := by
    calc
      (tupleLaw M tag xm).pr (EventAt u j) ≤
          ∑ F ∈ Families u j,
            (tupleLaw M tag xm).pr (fun W => ∀ D ∈ F,
              ¬ Valid M tag u ((xm, ym), W) D) :=
        pr_exists_finset_le_sum (tupleLaw M tag xm) (Families u j)
          (fun F W => ∀ D ∈ F, ¬ Valid M tag u ((xm, ym), W) D)
      _ ≤ ∑ _F ∈ Families u j, q ^ n := by
        apply Finset.sum_le_sum
        intro F hF
        have hFdata := (Finset.mem_filter.mp hF).1
        have hFspec := (Finset.mem_filter.mp hF).2
        have hFcard : F.card = n := (Finset.mem_powersetCard.mp hFdata).2
        have hsize : ∀ D ∈ F, 1 ≤ D.card ∧ D.card ≤ T := by
          intro D hD
          have hCandMem : D ∈ Cand u j := (Finset.mem_powersetCard.mp hFdata).1 hD
          have hCand' := hCandMem
          simp only [Cand, cands, Finset.mem_filter, Finset.mem_powerset] at hCand'
          simpa [T] using hCand'.2
        have h := tuple_all_invalid_prob_bound M tag hValid xm ym u F hsize hFspec
        simpa [q, hFcard] using h
      _ = (Families u j).card * q ^ n := by simp [Finset.sum_const]
      _ ≤ (n ^ (24 * T * n) : ℕ) * q ^ n :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hFamiliesBound u j) (by positivity)
  let Index : Finset (OddRole n × Fin (topH β γ n)) := Finset.univ
  have hOddCard : Fintype.card (OddRole n) ≤ 2 ^ n := by
    calc
      Fintype.card (OddRole n) ≤ Fintype.card (CubeVertex n) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      _ = 2 ^ n := by simp [CubeVertex]
  have hIndexCard : Index.card ≤ 2 ^ n * topH β γ n := by
    simp only [Index, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hOddCard
  have htop := topH_le_pow hβ hβγ hγ n (by omega)
  have hIndexPow : Index.card * n ^ (24 * T * n) ≤ n ^ (2 * n + 2 + 24 * T * n) := by
    calc
      Index.card * n ^ (24 * T * n) ≤ (2 ^ n * topH β γ n) * n ^ (24 * T * n) :=
        Nat.mul_le_mul_right _ hIndexCard
      _ ≤ (n ^ n * n ^ (n + 2)) * n ^ (24 * T * n) := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) n) htop
      _ = n ^ (n + (n + 2) + (24 * T * n)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
      _ = n ^ (2 * n + 2 + 24 * T * n) := by congr 1 <;> omega
  have hIndexReal : (Index.card : ℝ) * (n ^ (24 * T * n) : ℕ) ≤
      (n : ℝ) ^ (2 * n + 2 + 24 * T * n) := by exact_mod_cast hIndexPow
  have hposEvent :
      (tupleLaw M tag xm).pr
        (fun W => ∃ u : OddRole n, ∃ j : Fin (topH β γ n),
          n ≤ (marked M tag P ((xm, ym), W) u j).card) ≤
        (n : ℝ) ^ (2 * n + 2 + 24 * T * n) * q ^ n := by
    let Bad : (OddRole n × Fin (topH β γ n)) → Tuples β γ n N → Prop :=
      fun uj W => EventAt uj.1 uj.2 W
    have hsubset : ∀ W,
        (∃ u : OddRole n, ∃ j : Fin (topH β γ n),
          n ≤ (marked M tag P ((xm, ym), W) u j).card) →
        ∃ uj ∈ Index, Bad uj W := by
      intro W hW
      obtain ⟨u, j, hlarge⟩ := hW
      obtain ⟨F, hF, hbad⟩ := hMarkedFam W u j hlarge
      exact ⟨(u, j), Finset.mem_univ _, F, hF, hbad⟩
    have hmono : (tupleLaw M tag xm).pr
        (fun W => ∃ u : OddRole n, ∃ j : Fin (topH β γ n),
          n ≤ (marked M tag P ((xm, ym), W) u j).card) ≤
        (tupleLaw M tag xm).pr (fun W => ∃ uj ∈ Index, Bad uj W) :=
      pr_mono (tupleLaw M tag xm) hsubset
    have hunion := pr_exists_finset_le_sum (tupleLaw M tag xm) Index Bad
    calc
      _ ≤ (tupleLaw M tag xm).pr (fun W => ∃ uj ∈ Index, Bad uj W) := hmono
      _ ≤ ∑ uj ∈ Index, (tupleLaw M tag xm).pr (Bad uj) := hunion
      _ ≤ ∑ _uj ∈ Index, (n ^ (24 * T * n) : ℕ) * q ^ n := by
        apply Finset.sum_le_sum
        intro uj huj
        exact hEventAt uj.1 uj.2
      _ = (Index.card : ℝ) * (n ^ (24 * T * n) : ℕ) * q ^ n := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ (n : ℝ) ^ (2 * n + 2 + 24 * T * n) * q ^ n :=
        mul_le_mul_of_nonneg_right hIndexReal (by positivity)
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ε / ε := Real.log_natCast_le_rpow_div n hεpos
  have hB : 0 ≤ (n : ℝ) ^ ε / ε := by positivity
  have hnExp : (n : ℝ) ≤ Real.exp ((n : ℝ) ^ ε / ε) := by
    calc
      (n : ℝ) = Real.exp (Real.log (n : ℝ)) := by rw [Real.exp_log hnPos]
      _ ≤ Real.exp ((n : ℝ) ^ ε / ε) := Real.exp_le_exp.mpr hlog
  have hpowExp (k : ℕ) : (n : ℝ) ^ k ≤ Real.exp (((n : ℝ) ^ ε / ε) * k) := by
    calc
      (n : ℝ) ^ k ≤ Real.exp ((n : ℝ) ^ ε / ε) ^ k :=
        pow_le_pow_left₀ (by positivity) hnExp k
      _ = Real.exp (((n : ℝ) ^ ε / ε) * k) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ac_rfl
  have hTbig : 24 * (T : ℝ) * n ≤ 96 * (n : ℝ) ^ (1 + b) := by
    have hmul := mul_le_mul_of_nonneg_right hTle (show 0 ≤ 24 * (n : ℝ) by positivity)
    calc
      24 * (T : ℝ) * n = (T : ℝ) * (24 * (n : ℝ)) := by ring
      _ ≤ (4 * (n : ℝ) ^ b) * (24 * (n : ℝ)) := hmul
      _ = 96 * (n : ℝ) ^ (1 + b) := by
        rw [Real.rpow_add hnPos 1 b]
        rw [Real.rpow_one]
        ring
  have hlin : 2 * (n : ℝ) + 2 ≤ 4 * n := by linarith [hnR]
  have hbaseExp : 4 * n ≤ 4 * (n : ℝ) ^ (1 + b) := by
    have hnb : 1 ≤ (n : ℝ) ^ b := Real.one_le_rpow hnR hbpos.le
    rw [Real.rpow_add hnPos 1 b]
    rw [Real.rpow_one]
    have hmul := mul_le_mul_of_nonneg_left hnb (show 0 ≤ (n : ℝ) by positivity)
    nlinarith [hmul]
  have hK : (2 * n + 2 + 24 * T * n : ℕ) ≤ 100 * (n : ℝ) ^ (1 + b) := by
    push_cast
    linarith [hTbig, hlin, hbaseExp]
  have hKCast : (2 : ℝ) * n + 2 + 24 * (T : ℝ) * n ≤
      100 * (n : ℝ) ^ (1 + b) := by exact_mod_cast hK
  have hpowK : (n : ℝ) ^ (2 * n + 2 + 24 * T * n) ≤
      Real.exp (((n : ℝ) ^ ε / ε) * (2 * (n : ℝ) + 2 + 24 * (T : ℝ) * n)) := by
    have h := hpowExp (2 * n + 2 + 24 * T * n)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  have hEntropy :
      ((n : ℝ) ^ (2 * n + 2 + 24 * T * n)) ≤
        Real.exp (C * (n : ℝ) ^ (1 + b + ε)) := by
    calc
      (n : ℝ) ^ (2 * n + 2 + 24 * T * n) ≤
          Real.exp (((n : ℝ) ^ ε / ε) * (2 * (n : ℝ) + 2 + 24 * (T : ℝ) * n)) := hpowK
      _ ≤ Real.exp (C * (n : ℝ) ^ (1 + b + ε)) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_left hKCast hB
        calc
          (n : ℝ) ^ ε / ε * (2 * (n : ℝ) + 2 + 24 * (T : ℝ) * n) ≤
              (n : ℝ) ^ ε / ε * (100 * (n : ℝ) ^ (1 + b)) := hmul
          _ = C * (n : ℝ) ^ (1 + b + ε) := by
            dsimp [C]
            rw [Real.rpow_add hnPos (1 + b) ε]
            ring
  have hqPow : q ^ n = Real.exp (-((n : ℝ) ^ (1 + a))) := by
    dsimp [q, a]
    rw [← Real.exp_nat_mul]
    congr 1
    rw [Real.rpow_add hnPos 1 (omega4 β γ / 5)]
    rw [Real.rpow_one]
    ring
  have hδeq : b + ε + δ = a := by dsimp [b, ε, δ, a]; ring
  have hlargeExp : C * (n : ℝ) ^ (1 + b + ε) ≤ (n : ℝ) ^ (1 + a) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hGrowth
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 + b + ε))
    have hpower : 2 * (C * (n : ℝ) ^ (1 + b + ε)) ≤ (n : ℝ) ^ (1 + a) := by
      calc
        2 * (C * (n : ℝ) ^ (1 + b + ε)) =
            (n : ℝ) ^ (1 + b + ε) * (2 * C) := by ring
        _ ≤ (n : ℝ) ^ (1 + b + ε) * (n : ℝ) ^ δ := hmul
        _ = (n : ℝ) ^ (1 + b + ε + δ) := by rw [← Real.rpow_add hnPos]
        _ = (n : ℝ) ^ (1 + a) := by
          congr 1
          linarith [hδeq]
    nlinarith [hpower]
  have hqTail : Real.exp (C * (n : ℝ) ^ (1 + b + ε)) * q ^ n ≤ 1 / 30 := by
    have hlog30 : Real.log 30 ≤ 29 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 30)
      linarith
    have hnq : 30 ≤ (n : ℝ) ^ (1 + a) / 2 := by
      have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + a) := by
        rw [Real.rpow_add hnPos 1 a, Real.rpow_one]
        have hna : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hnR (by dsimp [a]; linarith [hωpos])
        nlinarith
      nlinarith [show (60 : ℝ) ≤ n by exact_mod_cast hn60, hpow]
    calc
      Real.exp (C * (n : ℝ) ^ (1 + b + ε)) * q ^ n =
          Real.exp (C * (n : ℝ) ^ (1 + b + ε) - (n : ℝ) ^ (1 + a)) := by rw [hqPow, ← Real.exp_add]; congr 1 <;> ring
      _ ≤ Real.exp (-Real.log 30) := Real.exp_le_exp.mpr (by linarith [hlargeExp, hnq, hlog30])
      _ = 1 / 30 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 30)]; norm_num
  calc
    (tupleLaw M tag xm).pr
        (fun W => ∃ u : OddRole n, ∃ j : Fin (topH β γ n),
          n ≤ (marked M tag P ((xm, ym), W) u j).card) ≤
        (n : ℝ) ^ (2 * n + 2 + 24 * T * n) * q ^ n := by exact_mod_cast hposEvent
    _ ≤ Real.exp (C * (n : ℝ) ^ (1 + b + ε)) * q ^ n :=
      mul_le_mul_of_nonneg_right hEntropy (by positivity)
    _ ≤ 1 / 30 := hqTail

/-- The count-concentration union bound is below `1/30` beyond one explicit threshold. -/
theorem count_tail_bound {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1)
    (n : ℕ) (hn : 22 ^ 11 ≤ n) :
    2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
        ((topH β γ n + 1 : ℕ) : ℝ) * Real.exp (-lamH n / 12) ≤ 1 / 30 := by
  have hn4 : 4 ≤ n := by omega
  have hH := topH_le_pow hβ hβγ hγ n hn4
  have hHplus : topH β γ n + 1 ≤ n ^ (n + 3) := by
    have hpowpos : 1 ≤ n ^ (n + 2) := Nat.one_le_pow (n + 2) n (by omega)
    calc
      topH β γ n + 1 ≤ n ^ (n + 2) + 1 := Nat.add_le_add_right hH 1
      _ ≤ 2 * n ^ (n + 2) := by omega
      _ ≤ n * n ^ (n + 2) := Nat.mul_le_mul_right _ (by omega)
      _ = n ^ (n + 3) := by rw [Nat.pow_succ]; ring
  have hsiteEq : (Finset.univ : Finset (CubeVertex n)).card = 2 ^ n := by
    simp [CubeVertex]
  have hsite : ((Finset.univ : Finset (CubeVertex n)).card : ℝ) ≤ (n : ℝ) ^ n := by
    rw [hsiteEq]
    exact_mod_cast (Nat.pow_le_pow_left (show 2 ≤ n by omega) n)
  have hheight : ((topH β γ n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ (n + 3) := by
    exact_mod_cast hHplus
  have hnexp : (n : ℝ) ≤ Real.exp (n : ℝ) := by
    have h := Real.add_one_le_exp (n : ℝ)
    linarith
  have hpowExp (k : ℕ) : (n : ℝ) ^ k ≤ Real.exp ((n : ℝ) * k) := by
    calc
      (n : ℝ) ^ k ≤ Real.exp (n : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hnexp k
      _ = Real.exp ((n : ℝ) * k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hnpoly : (1 : ℝ) + (n : ℝ) * n + (n : ℝ) * ((n : ℝ) + 3) ≤ (n : ℝ) ^ 4 := by
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
    have hnSq : 16 ≤ (n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 4)]
    have hnFourth : 16 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
      have h := mul_le_mul_of_nonneg_right hnSq (sq_nonneg (n : ℝ))
      nlinarith [h]
    nlinarith [hnFourth, hnR]
  have hfactor : 2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
      ((topH β γ n + 1 : ℕ) : ℝ) ≤ Real.exp ((n : ℝ) ^ 4) := by
    calc
      2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
          ((topH β γ n + 1 : ℕ) : ℝ) ≤
          2 * (n : ℝ) ^ n * (n : ℝ) ^ (n + 3) := by gcongr
      _ ≤ Real.exp 1 * Real.exp ((n : ℝ) * n) *
          Real.exp ((n : ℝ) * (n + 3)) := by
            have hfirst : 2 * (n : ℝ) ^ n ≤ Real.exp 1 * Real.exp ((n : ℝ) * n) :=
              mul_le_mul h2exp (hpowExp n) (by positivity) (Real.exp_nonneg _)
            exact mul_le_mul hfirst (by simpa [Nat.cast_add] using hpowExp (n + 3))
              (by positivity) (by positivity)
      _ = Real.exp (1 + (n : ℝ) * n + (n : ℝ) * ((n : ℝ) + 3)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((n : ℝ) ^ 4) := Real.exp_le_exp.mpr hnpoly
  have hlam : lamH n = (n : ℝ) ^ 10 := by simp [lamH]
  have hnSix : 24 ≤ (n : ℝ) ^ 6 := by
    have hNat : 64 ≤ n ^ 6 := by
      calc
        64 = 2 ^ 6 := by norm_num
        _ ≤ n ^ 6 := Nat.pow_le_pow_left (by omega) 6
    exact_mod_cast (le_trans (by norm_num) hNat)
  have hlarge : (n : ℝ) ^ 4 + Real.log 30 ≤ (n : ℝ) ^ 10 / 12 := by
    have hlog30 : Real.log 30 ≤ 29 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 30)
      linarith
    have hnFour : 29 ≤ (n : ℝ) ^ 4 := by
      have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      nlinarith [sq_nonneg ((n : ℝ) - 4)]
    have hmul := mul_le_mul_of_nonneg_left hnSix (show 0 ≤ (n : ℝ) ^ 4 by positivity)
    have hpow : 2 * (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 10 / 12 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 12)).2
      calc
        2 * (n : ℝ) ^ 4 * 12 = 24 * (n : ℝ) ^ 4 := by ring
        _ ≤ (n : ℝ) ^ 6 * (n : ℝ) ^ 4 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        _ = (n : ℝ) ^ 10 := by rw [← pow_add]
    linarith
  calc
    2 * ((Finset.univ : Finset (CubeVertex n)).card : ℝ) *
        ((topH β γ n + 1 : ℕ) : ℝ) * Real.exp (-lamH n / 12) ≤
        Real.exp ((n : ℝ) ^ 4) * Real.exp (-((n : ℝ) ^ 10) / 12) := by
          rw [hlam]
          exact mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) ^ 4 - (n : ℝ) ^ 10 / 12) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (-(Real.log 30)) := Real.exp_le_exp.mpr (by linarith [hlarge])
    _ = 1 / 30 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 30)]
      norm_num

/-- The deterministic eligibility statement derived from the forbidden-card bound. -/
theorem geo_legal_proof {β γ : ℝ} (hβ : 0 < β) (hβγ : β ≤ γ) (hγ : γ < 1) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
      {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι),
      LegalOf M tag := by
  refine ⟨2, ?_⟩
  intro n hn N E G X Y M tag ω hcounts hfamilies
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hω := omega4_lt hβ hβγ
  have hb : bH β γ ≤ 1 := by dsimp [bH]; linarith
  have hpow : (n : ℝ) ^ bH β γ ≤ n := by
    calc
      (n : ℝ) ^ bH β γ ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 hb
      _ = n := by simp
  have hLam : lamH n = (n : ℝ) ^ 10 := by simp [lamH]
  have hset : setBd β γ n ≤ 4 * n := by
    apply Nat.ceil_le.mpr
    calc
      3 * (n : ℝ) ^ bH β γ ≤ 3 * n :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ (4 * n : ℕ) := by exact_mod_cast (show 3 * n ≤ 4 * n by omega)
  intro v hv l
  let Raw : Finset (Loc β γ n) := Finset.univ.filter fun c =>
    ppos ω c = true ∧ c.2 = l ∧ hammingDist c.1 v ≤ radius β γ n
  let F : Finset (Loc β γ n) := forbidden M tag (ppos ω) (paux ω) v l
  have hFNat : F.card ≤ 2 * n ^ 2 * setBd β γ n :=
    forbidden_card_le M tag (ppos ω) (paux ω) v l hfamilies
  have hFReal : (F.card : ℝ) ≤ lamH n / 6 := by
    have hF' : (F.card : ℝ) ≤ 2 * (n : ℝ) ^ 2 * (setBd β γ n : ℝ) := by
      exact_mod_cast hFNat
    have hsetR : (setBd β γ n : ℝ) ≤ 4 * n := by exact_mod_cast hset
    have hn7 : 48 ≤ n ^ 7 := by
      have hpowN : 2 ^ 7 ≤ n ^ 7 := by gcongr
      norm_num at hpowN ⊢
      omega
    have hn7R : (48 : ℝ) ≤ (n : ℝ) ^ 7 := by exact_mod_cast hn7
    have hn10 : 8 * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 10 / 6 := by
      nlinarith [mul_le_mul_of_nonneg_left hn7R (show 0 ≤ (n : ℝ) ^ 3 by positivity)]
    have hbound : (F.card : ℝ) ≤ (n : ℝ) ^ 10 / 6 := calc
      (F.card : ℝ) ≤ 2 * (n : ℝ) ^ 2 * (setBd β γ n : ℝ) := hF'
      _ ≤ 2 * (n : ℝ) ^ 2 * (4 * n) := by gcongr
      _ = 8 * (n : ℝ) ^ 3 := by ring
      _ ≤ (n : ℝ) ^ 10 / 6 := hn10
    simpa [hLam] using hbound
  have hRawCard : Raw.card = countAt (ppos ω) v l := by
    dsimp [Raw]
    exact rawAt_card_eq_countAt (ppos ω) v l
  have hEeq : elig M tag (ppos ω) (paux ω) v l = Raw \ F := by
    rfl
  have hRawCover : Raw.card ≤ (Raw \ F).card + F.card := by
    have hsub : Raw ⊆ (Raw \ F) ∪ F := by
      intro c hc
      by_cases hFc : c ∈ F
      · exact Finset.mem_union.mpr (Or.inr hFc)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hc, hFc⟩))
    calc
      Raw.card ≤ ((Raw \ F) ∪ F).card := Finset.card_le_card hsub
      _ ≤ (Raw \ F).card + F.card := Finset.card_union_le _ _
  have hRawReal : lamH n / 2 ≤ (Raw.card : ℝ) := by
    simpa [hRawCard] using hcounts v l
  have hEligCard : lamH n / 3 ≤ ((elig M tag (ppos ω) (paux ω) v l).card : ℝ) := by
    have hCover : (Raw.card : ℝ) ≤
        ((elig M tag (ppos ω) (paux ω) v l).card : ℝ) + (F.card : ℝ) := by
      have hCoverNat : Raw.card ≤
          (elig M tag (ppos ω) (paux ω) v l).card + F.card := by
        rw [hEeq]
        exact hRawCover
      exact_mod_cast hCoverNat
    rw [hEeq] at hCover
    rw [hEeq]
    rw [hLam] at hRawReal ⊢
    have hFReal' : (F.card : ℝ) ≤ (n : ℝ) ^ 10 / 6 := by simpa [hLam] using hFReal
    have hLow : 3 * (n : ℝ) ^ 10 ≤ 6 * (Raw.card : ℝ) := by
      linarith [hRawReal]
    have hMid : 6 * (Raw.card : ℝ) ≤
        6 * ((Raw \ F).card : ℝ) + 6 * (F.card : ℝ) := by
      nlinarith [hCover]
    have hHigh : 6 * (F.card : ℝ) ≤ (n : ℝ) ^ 10 := by
      nlinarith [hFReal']
    have hContradiction : 3 * (n : ℝ) ^ 10 ≤
        6 * ((Raw \ F).card : ℝ) + (n : ℝ) ^ 10 := by
      calc
        3 * (n : ℝ) ^ 10 ≤ 6 * (Raw.card : ℝ) := hLow
        _ ≤ 6 * ((Raw \ F).card : ℝ) + 6 * (F.card : ℝ) := hMid
        _ ≤ 6 * ((Raw \ F).card : ℝ) + (n : ℝ) ^ 10 := by linarith [hHigh]
    by_contra hnot
    have hElt : ((Raw \ F).card : ℝ) < (n : ℝ) ^ 10 / 3 := lt_of_not_ge hnot
    have hElt' : 6 * ((Raw \ F).card : ℝ) < 2 * (n : ℝ) ^ 10 := by
      nlinarith [hElt]
    nlinarith [hContradiction, hElt']
  have hlegal : ∀ c ∈ elig M tag (ppos ω) (paux ω) v l,
      ppos ω c = true ∧ c.2 = l ∧ hammingDist c.1 v ≤ radius β γ n := by
    intro c hc
    have hcRaw : c ∈ Raw := (Finset.mem_sdiff.mp (by simpa [hEeq] using hc)).1
    exact (Finset.mem_filter.mp hcRaw).2
  exact ⟨hlegal, by simpa using hEligCard⟩

/-- Every cube neighbor is obtained by flipping its unique differing coordinate. -/
theorem cube_neighbor_flip {n : ℕ} (u v : CubeVertex n) (h : (cube n).Adj u v) :
    ∃ j : Fin n, v = cubeFlip u j := by
  classical
  have hcard : (Finset.univ.filter fun i : Fin n => u i ≠ v i).card = 1 := by
    change _ = 1 at h
    exact h
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, ?_⟩
  funext i
  by_cases hi : i = j
  · subst i
    have hjmem : j ∈ Finset.univ.filter fun i : Fin n => u i ≠ v i := by
      rw [hj]
      simp
    have hne := (Finset.mem_filter.mp hjmem).2
    cases hu : u j <;> cases hv : v j <;> simp_all [cubeFlip]
  · have hinot : i ∉ Finset.univ.filter fun i : Fin n => u i ≠ v i := by
      rw [hj]
      simpa using hi
    have heq : u i = v i := by
      by_contra hne
      exact hinot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    simp [cubeFlip, hi, heq]

/-- An odd role can exist only in positive cube dimension. -/
theorem odd_role_posdim {n : ℕ} (u : OddRole n) : 0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst n
  exact u.2 (by simp [IsEvenRole])

/-- A neighbor of an odd role is an even site. -/
theorem oddAdj_even {n : ℕ} (u : OddRole n) {v : CubeVertex n} (hv : v ∈ oddAdj u) :
    IsEvenRole v := by
  have hadj : (cube n).Adj u.1 v := by simpa [oddAdj] using hv
  obtain ⟨j, rfl⟩ := cube_neighbor_flip u.1 v hadj
  exact (cubeFlip_parity u.1 j).2 u.2

/-- Two neighbors of one cube vertex have distance at most two. -/
theorem oddAdj_dist_le_two {n : ℕ} (u : OddRole n) {v w : CubeVertex n}
    (hv : v ∈ oddAdj u) (hw : w ∈ oddAdj u) : _root_.hammingDist v w ≤ 2 := by
  have hvAdj : (cube n).Adj u.1 v := by simpa [oddAdj] using hv
  have hwAdj : (cube n).Adj u.1 w := by simpa [oddAdj] using hw
  have h₁ : _root_.hammingDist v u.1 = 1 := by
    have h := ((cube n).adj_comm u.1 v).mp hvAdj
    simpa [cube] using h
  have h₂ : _root_.hammingDist u.1 w = 1 := by simpa [cube] using hwAdj
  exact (_root_.hammingDist_triangle v u.1 w).trans (by omega)

/-- The selected center at a good site is active and belongs to that height's eligibility set. -/
theorem sel_mem_elig {β γ : ℝ} {G : Colour} {n N : ℕ} {E : Fin N → Fin N → Prop}
    {X Y : Finset (Fin N)} (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ω : Prep M tag) (v : CubeVertex n)
    (hv : v ∈ evenSites n)
    (hgood : (hd β γ n).GoodHeights (evenSites n) (ppos ω) (pact ω)
      (elig M tag (ppos ω) (paux ω)))
    {c : Loc β γ n} (hsel : sel M tag ω v = some c) :
    c ∈ elig M tag (ppos ω) (paux ω) v
        ⟨(hd β γ n).height (evenSites n) (ppos ω) (pact ω)
          (elig M tag (ppos ω) (paux ω)) (hd β γ n).Rlong v,
          by
            exact Nat.lt_succ_of_lt (hgood v hv).1⟩ ∧ pact ω c = true := by
  classical
  let p := hd β γ n
  have hgh := hgood v hv
  have hh : p.height (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))
      p.Rlong v < p.H := by simpa [p, hd] using hgh.1
  let l : Fin (p.H + 1) := ⟨p.height (evenSites n) (ppos ω) (pact ω)
    (elig M tag (ppos ω) (paux ω)) p.Rlong v, Nat.lt_succ_of_lt hh⟩
  have hbad : ¬ p.Bad (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω)) v l := by
    intro hb
    exact hgh.2.1 ⟨Nat.lt_succ_of_lt hh, hb⟩
  have hs : p.selection (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))
      (pties ω) v = some c := by simpa [sel, p] using hsel
  simp [HDParams.selection, HDParams.selectionAt, l, hh, hbad] at hs
  rcases hs with ⟨hactive, hchosen⟩
  let active := (elig M tag (ppos ω) (paux ω) v l).filter (fun ℓ => pact ω ℓ = true)
  let priorities := active.image (p.priority (pties ω) (v, l))
  have hneP : priorities.Nonempty := by
    rcases hactive with ⟨ℓ, hℓ⟩
    exact ⟨p.priority (pties ω) (v, l) ℓ,
      Finset.mem_image.mpr ⟨ℓ, by simpa [active] using hℓ, rfl⟩⟩
  let q := priorities.min' hneP
  have hmem : ∃ ℓ, ℓ ∈ active ∧ p.priority (pties ω) (v, l) ℓ = q :=
    Finset.mem_image.mp (Finset.min'_mem priorities hneP)
  have hchosen' : Classical.choose hmem = c := by
    simpa [q, active, priorities, l] using hchosen
  rcases Classical.choose_spec hmem with ⟨hmemActive, hprio⟩
  rw [hchosen'] at hmemActive
  exact ⟨(Finset.mem_filter.mp hmemActive).1, (Finset.mem_filter.mp hmemActive).2⟩

/-- Good heights make the selected kernel at each odd role a valid marked candidate. -/
theorem geo_oddOK_proof {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (hSel : SelectOf M tag) : OddOKOf M tag := by
  classical
  intro ω hgood u
  let p := hd β γ n
  let P := ppos ω
  let A := pact ω
  let aux := paux ω
  let D := selSet M tag ω u
  have hgoodP : p.GoodHeights (evenSites n) P A (elig M tag P aux) := by
    simpa [p, P, A, aux] using hgood
  have hselAll : ∀ v ∈ oddAdj u, sel M tag ω v ≠ none := by
    intro v hv
    have heven := oddAdj_even u hv
    have hsite : v ∈ evenSites n := by simp [evenSites, heven]
    simpa using hSel ω hgood ⟨v, heven⟩
  have hn : 0 < n := odd_role_posdim u
  let i0 : Fin n := ⟨0, hn⟩
  let v0 : CubeVertex n := cubeFlip u.1 i0
  have hv0 : v0 ∈ oddAdj u := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, cubeFlip_adj u.1 i0⟩
  have hev0 := oddAdj_even u hv0
  have hv0site : v0 ∈ evenSites n := by simp [evenSites, hev0]
  have hs0 : sel M tag ω v0 ≠ none := hselAll v0 hv0
  obtain ⟨c0, hc0⟩ := Option.ne_none_iff_exists'.mp hs0
  have hc0set : c0 ∈ (sel M tag ω v0).toFinset := by simpa [hc0]
  have hc0D : c0 ∈ D := by
    exact Finset.mem_biUnion.mpr ⟨v0, hv0, hc0set⟩
  have hDpos : 1 ≤ D.card := by
    have hDpos' : 0 < D.card := Finset.card_pos.mpr ⟨c0, hc0D⟩
    omega
  let ht : CubeVertex n → ℕ := fun v =>
    p.height (evenSites n) P A (elig M tag P aux) p.Rlong v
  have h0top : ht v0 < p.H := by
    simpa [ht] using (hgoodP v0 hv0site).1
  have hsite (v : CubeVertex n) (hv : v ∈ oddAdj u) : v ∈ evenSites n :=
    by simp [evenSites, oddAdj_even u hv]
  have hHtBound : ∀ v ∈ oddAdj u, ht v < p.H := by
    intro v hv
    simpa [ht] using (hgoodP v (hsite v hv)).1
  have hgap : ∀ v ∈ oddAdj u, ∀ w ∈ oddAdj u,
      |(ht v : ℤ) - (ht w : ℤ)| ≤ 1 := by
    intro v hv w hw
    have hdist := oddAdj_dist_le_two u hv hw
    have hdist' : _root_.hammingDist v w ≤ p.D := by simpa [hd] using hdist
    simpa [ht] using (hgoodP v (hsite v hv)).2.2 w (hsite w hw) hdist'
  have hdiffLe : ∀ v ∈ oddAdj u, ∀ w ∈ oddAdj u,
      ht v ≤ ht w + 1 ∧ ht w ≤ ht v + 1 := by
    intro v hv w hw
    have habs := abs_le.mp (hgap v hv w hw)
    constructor <;> omega
  have hlevels : ∃ j : Fin (topH β γ n), j.val < p.H ∧
      ∀ v ∈ oddAdj u, ht v = j.val ∨ ht v = j.val + 1 := by
    by_cases hlower : ∃ v ∈ oddAdj u, ht v < ht v0
    · obtain ⟨w0, hw0, hlt0⟩ := hlower
      have hgap0 := hgap w0 hw0 v0 hv0
      have hbounds0 := hdiffLe w0 hw0 v0 hv0
      have hEq0 : ht v0 = ht w0 + 1 := by omega
      have hw0lt : ht w0 < p.H := by
        simpa [ht] using (hgoodP w0 (hsite w0 hw0)).1
      have hw0ltTop : ht w0 < topH β γ n := by simpa [p, hd] using hw0lt
      refine ⟨⟨ht w0, hw0ltTop⟩, ?_, ?_⟩
      · change ht w0 < p.H
        exact hw0lt
      intro v hv
      have hgapV0 := hdiffLe v hv v0 hv0
      have hgapVW := hdiffLe w0 hw0 v hv
      change ht v = ht w0 ∨ ht v = ht w0 + 1
      omega
    · have h0top' : ht v0 < topH β γ n := by simpa [p, hd] using h0top
      refine ⟨⟨ht v0, h0top'⟩, ?_, ?_⟩
      · change ht v0 < p.H
        exact h0top
      intro v hv
      have hgapV0 := hdiffLe v hv v0 hv0
      have hnotlower : ¬ ht v < ht v0 := by
        intro hlt
        exact hlower ⟨v, hv, hlt⟩
      change ht v = ht v0 ∨ ht v = ht v0 + 1
      omega
  obtain ⟨j, hjtop, hjlevels⟩ := hlevels
  have hDsub : D ⊆ pool P u j := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hcOpt⟩
    have hs : sel M tag ω v = some c := by simpa using hcOpt
    have hmem := sel_mem_elig M tag ω v (hsite v hv) hgood hs
    have hraw : c ∈ Finset.univ.filter fun z : Loc β γ n =>
        P z = true ∧ z.2 = ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ ∧
          _root_.hammingDist z.1 v ≤ radius β γ n := by
      have hmem' : c ∈ elig M tag P aux v ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ := hmem.1
      exact (Finset.mem_sdiff.mp (by simpa [elig] using hmem')).1
    have hraw' := (Finset.mem_filter.mp hraw).2
    have hP : P c = true := hraw'.1
    have hlevel : c.2.val = ht v := by
      have heq := hraw'.2.1
      exact congrArg Fin.val heq
    have hdist : _root_.hammingDist c.1 v ≤ radius β γ n := hraw'.2.2
    have hpair := hjlevels v hv
    have hpair' : c.2.val = j.val ∨ c.2.val = j.val + 1 := by omega
    simp only [pool, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hP, hpair', ⟨v, hv, hdist⟩⟩
  have hDsubsetLevels : D ⊆
      (D.filter fun c => c.2.val = j.val) ∪
        (D.filter fun c => c.2.val = j.val + 1) := by
    intro c hc
    have hpool := hDsub hc
    have hlevpair := (Finset.mem_filter.mp hpool).2.2.1
    rcases hlevpair with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hc, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hc, h⟩))
  let q0 : Fin (topH β γ n + 1) := ⟨j.val, by omega⟩
  let q1 : Fin (topH β γ n + 1) := ⟨j.val + 1, by omega⟩
  let D0 : Finset (Loc β γ n) := D.filter fun c => c.2 = q0
  let D1 : Finset (Loc β γ n) := D.filter fun c => c.2 = q1
  have hboundLevel : ∀ (q : Fin (topH β γ n + 1)) (S : Finset (Loc β γ n)),
      S ⊆ D → (∀ c ∈ S, c.2 = q) → (S.card : ℝ) ≤ (n : ℝ) ^ bH β γ := by
    intro q S hS hlevelS
    by_cases hSne : S.Nonempty
    · obtain ⟨c0, hc0S⟩ := hSne
      have hc0D : c0 ∈ D := hS hc0S
      rcases Finset.mem_biUnion.mp hc0D with ⟨v0', hv0', hc0Opt'⟩
      have hs0' : sel M tag ω v0' = some c0 := by simpa using hc0Opt'
      have hmem0' := sel_mem_elig M tag ω v0' (hsite v0' hv0') hgood hs0'
      have hraw0' : c0 ∈ Finset.univ.filter fun z : Loc β γ n =>
          P z = true ∧ z.2 = ⟨ht v0', Nat.lt_succ_of_lt (hHtBound v0' hv0')⟩ ∧
            _root_.hammingDist z.1 v0' ≤ radius β γ n := by
        have hmem' : c0 ∈ elig M tag P aux v0' ⟨ht v0', Nat.lt_succ_of_lt (hHtBound v0' hv0')⟩ := hmem0'.1
        exact (Finset.mem_sdiff.mp (by simpa [elig] using hmem')).1
      have hraw0'' := (Finset.mem_filter.mp hraw0').2
      have hqval : ht v0' = q.val := by
        have h1 : c0.2 = ⟨ht v0', Nat.lt_succ_of_lt (hHtBound v0' hv0')⟩ := hraw0''.2.1
        have h2 := hlevelS c0 hc0S
        calc
          ht v0' = c0.2.val := (congrArg Fin.val h1).symm
          _ = q.val := congrArg Fin.val h2
      have hWgood := hgoodP v0' (hsite v0' hv0')
      have hheightTop : ht v0' < p.H := hHtBound v0' hv0'
      have hqtop : q.val < p.H := by omega
      have hnotBad : ¬ p.Bad P A (elig M tag P aux) v0' q := by
        intro hbad
        apply hWgood.2.1
        have hqFin : (⟨ht v0', Nat.lt_succ_of_lt hheightTop⟩ : Fin (p.H + 1)) = q := by
          apply Fin.ext
          omega
        have hbad' : p.Bad P A (elig M tag P aux) v0'
            ⟨ht v0', Nat.lt_succ_of_lt hheightTop⟩ := by
          rw [hqFin]
          exact hbad
        exact ⟨Nat.lt_succ_of_lt hheightTop, hbad'⟩
      let Crowd : Finset (CubeVertex n) := Finset.univ.filter fun x =>
        P (x, q) = true ∧ A (x, q) = true ∧
          _root_.hammingDist x v0' ≤ radius β γ n + 2
      have hCrowd : (Crowd.card : ℝ) ≤ (n : ℝ) ^ bH β γ := by
        by_contra hnot
        have hgt : (n : ℝ) ^ bH β γ < (Crowd.card : ℝ) := lt_of_not_ge hnot
        apply hnotBad
        apply Or.inr
        simpa [HDParams.Bad, p, hd, Crowd, P, A, aux] using hgt
      have himageSub : (S.image Prod.fst) ⊆ Crowd := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨c, hcS, rfl⟩
        have hcD' : c ∈ D := hS hcS
        rcases Finset.mem_biUnion.mp hcD' with ⟨v, hv, hcOpt⟩
        have hs : sel M tag ω v = some c := by simpa using hcOpt
        have hmem := sel_mem_elig M tag ω v (hsite v hv) hgood hs
        have hraw : c ∈ Finset.univ.filter fun z : Loc β γ n =>
            P z = true ∧ z.2 = ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ ∧
              _root_.hammingDist z.1 v ≤ radius β γ n := by
          have hmem' : c ∈ elig M tag P aux v ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ := hmem.1
          exact (Finset.mem_sdiff.mp (by simpa [elig] using hmem')).1
        have hraw' := (Finset.mem_filter.mp hraw).2
        have hq' : ht v = q.val := by
          have h1 := congrArg Fin.val hraw'.2.1
          have h2 := congrArg Fin.val (hlevelS c hcS)
          calc
            ht v = c.2.val := h1.symm
            _ = q.val := h2
        have hdvw : _root_.hammingDist v v0' ≤ 2 := oddAdj_dist_le_two u hv hv0'
        have hdist : _root_.hammingDist c.1 v0' ≤ radius β γ n + 2 := by
          exact (_root_.hammingDist_triangle c.1 v v0').trans (by omega)
        have hlevFin : c.2 = q := hlevelS c hcS
        have heq : c = (c.1, q) := Prod.ext rfl hlevFin
        have heq' : (c.1, q) = c := heq.symm
        have hpq : P (c.1, q) = true := by rw [heq']; exact hraw'.1
        have hA' : A c = true := by simpa [A] using hmem.2
        have haq : A (c.1, q) = true := by rw [heq']; exact hA'
        simp only [Crowd, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hpq, haq, hdist⟩
      have hinj : Set.InjOn Prod.fst (S : Set (Loc β γ n)) := by
        intro c hc c' hc' heq
        exact Prod.ext heq ((hlevelS c hc).trans (hlevelS c' hc').symm)
      have hcardImg : (S.image Prod.fst).card = S.card := Finset.card_image_iff.mpr hinj
      have hcardNat : S.card ≤ Crowd.card := by
        calc
          S.card = (S.image Prod.fst).card := hcardImg.symm
          _ ≤ Crowd.card := Finset.card_le_card himageSub
      have hcardReal : (S.card : ℝ) ≤ (Crowd.card : ℝ) := by exact_mod_cast hcardNat
      exact hcardReal.trans hCrowd
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
      have hpowNonneg : 0 ≤ (n : ℝ) ^ bH β γ := by positivity
      simpa [hSempty] using hpowNonneg
  have hD0bound : (D0.card : ℝ) ≤ (n : ℝ) ^ bH β γ :=
    hboundLevel q0 D0 (Finset.filter_subset _ _) (by intro c hc; exact (Finset.mem_filter.mp hc).2)
  have hD1bound : (D1.card : ℝ) ≤ (n : ℝ) ^ bH β γ :=
    hboundLevel q1 D1 (Finset.filter_subset _ _) (by intro c hc; exact (Finset.mem_filter.mp hc).2)
  have hDcover : D ⊆ D0 ∪ D1 := by
    intro c hc
    have hpair := hDsubsetLevels hc
    rcases Finset.mem_union.mp hpair with h | h
    · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr
        ⟨hc, Fin.ext (Finset.mem_filter.mp h).2⟩
    · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr
        ⟨hc, Fin.ext (Finset.mem_filter.mp h).2⟩
  have hDcard : (D.card : ℝ) ≤ 2 * (n : ℝ) ^ bH β γ := by
    have hNat : D.card ≤ D0.card + D1.card := by
      calc
        D.card ≤ (D0 ∪ D1).card := Finset.card_le_card hDcover
        _ ≤ D0.card + D1.card := Finset.card_union_le _ _
    have hCast : (D.card : ℝ) ≤ (D0.card : ℝ) + (D1.card : ℝ) := by exact_mod_cast hNat
    nlinarith [hCast, hD0bound, hD1bound]
  have hceil : 3 * (n : ℝ) ^ bH β γ ≤ (setBd β γ n : ℝ) := by
    simpa [setBd] using (Nat.le_ceil (3 * (n : ℝ) ^ bH β γ))
  have hDcardLe : D.card ≤ setBd β γ n := by
    have hReal : (D.card : ℝ) ≤ (setBd β γ n : ℝ) := by
      calc
        (D.card : ℝ) ≤ 2 * (n : ℝ) ^ bH β γ := hDcard
        _ ≤ 3 * (n : ℝ) ^ bH β γ := by
          nlinarith [show 0 ≤ (n : ℝ) ^ bH β γ by positivity]
        _ ≤ (setBd β γ n : ℝ) := hceil
    exact_mod_cast hReal
  have hDcand : D ∈ cands P u j := by
    simp only [cands, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hDsub, ⟨hDpos, hDcardLe⟩⟩
  have hValid : Valid M tag u aux D := by
    by_contra hNotValid
    let L := ((cands P u j).filter fun F => ¬ Valid M tag u aux F).toList
    have hDList : D ∈ L := by
      simp [L, hDcand, hNotValid]
    obtain ⟨F, hF, hFnotDisj⟩ := (greedy_spec L).2.2 D hDList ⟨c0, hc0D⟩
    have hFmarked : F ∈ marked M tag P aux u j := by simpa [marked, L] using hF
    obtain ⟨c, hcF, hcD⟩ := Finset.not_disjoint_iff.mp hFnotDisj
    rcases Finset.mem_biUnion.mp hcD with ⟨v, hv, hcOpt⟩
    have hs : sel M tag ω v = some c := by simpa using hcOpt
    have hsiteV := hsite v hv
    have hmemSel := sel_mem_elig M tag ω v hsiteV hgood hs
    have hforbid : c ∈ forbidden M tag P aux v c.2 := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ⟨rfl, u, hv, j, F, hFmarked, hcF⟩⟩
    have hnotForbid : c ∉ forbidden M tag P aux v c.2 := by
      have hraw : c ∈ Finset.univ.filter fun z : Loc β γ n =>
          P z = true ∧ z.2 = ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ ∧
            _root_.hammingDist z.1 v ≤ radius β γ n := by
        have hmem' : c ∈ elig M tag P aux v ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ := hmemSel.1
        exact (Finset.mem_sdiff.mp (by simpa [elig] using hmem')).1
      have hEq : c.2 = ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ :=
        (Finset.mem_filter.mp hraw).2.2.1
      have hDiff : c ∈ (Finset.univ.filter fun z : Loc β γ n =>
          P z = true ∧ z.2 = ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ ∧
            _root_.hammingDist z.1 v ≤ radius β γ n) \
          forbidden M tag P aux v ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ := by
        simpa [elig] using hmemSel.1
      have hnotAt : c ∉ forbidden M tag P aux v ⟨ht v, Nat.lt_succ_of_lt (hHtBound v hv)⟩ :=
        (Finset.mem_sdiff.mp hDiff).2
      intro hforbid
      apply hnotAt
      simpa [hEq] using hforbid
    exact hnotForbid hforbid
  exact ⟨hselAll, hValid⟩

end HypercubeRamsey.Lane_q_s04_geom
