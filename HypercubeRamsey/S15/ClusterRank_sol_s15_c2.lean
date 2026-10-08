import HypercubeRamsey.S15.ClusterReverse_sol_s15_transfer
import HypercubeRamsey.S15.MaskSummation_sol_s15_mask
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace HypercubeRamsey.Lane_sol_s15_c2

open HypercubeRamsey.S15 Classical Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem forest_probability_le {V X I : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [DecidableEq I] (P : FinLaw X) (near : X → X → Prop)
    (p : ℝ) (hp : 0 ≤ p) (hnear : ∀ y, P.pr (fun x => near x y) ≤ p)
    (u v : I → V) (r : V → ℕ) (S : Finset I)
    (hu : Set.InjOn u S) (hr : ∀ t ∈ S, r (v t) < r (u t)) :
    (FinLaw.pi (fun _ : V => P)).pr (fun xs => ∀ t ∈ S, near (xs (u t)) (xs (v t))) ≤ p ^ S.card := by
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hS : S.Nonempty
  · obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image S (fun t => r (u t)) hS
    let R := S.erase t
    have hRsub : R ⊆ S := Finset.erase_subset _ _
    have hRss : R ⊂ S := Finset.erase_ssubset ht
    have hne (s) (hs : s ∈ R) : u s ≠ u t := by
      intro heq
      have hst := hu (hRsub hs) ht heq
      exact (Finset.mem_erase.mp hs).1 hst
    have hvne (s) (hs : s ∈ R) : v s ≠ u t := by
      intro heq
      have hlt := hr s (hRsub hs)
      rw [heq] at hlt
      exact (Nat.not_lt_of_ge (hmax s (hRsub hs))) hlt
    let F : (V → X) → ℝ := fun xs => if ∀ s ∈ R, near (xs (u s)) (xs (v s)) then 1 else 0
    let A : (V → X) → Prop := fun xs => near (xs (u t)) (xs (v t))
    have hskip (xs : V → X) (x : X) : F (Function.update xs (u t) x) = F xs := by
      have heq : (∀ s ∈ R, near ((Function.update xs (u t) x) (u s))
        ((Function.update xs (u t) x) (v s))) ↔ ∀ s ∈ R, near (xs (u s)) (xs (v s)) := by
        apply forall₂_congr
        intro s hs
        rw [Function.update_of_ne (hne s hs), Function.update_of_ne (hvne s hs)]
      simp only [F, heq]
    have hcharge (xs : V → X) : P.pr (fun x => A (Function.update xs (u t) x)) ≤ p := by
      have hv : v t ≠ u t := by intro heq; have h := hr t ht; rw [heq] at h; omega
      simpa [A, Function.update_of_ne hv] using hnear (xs (v t))
    have hpoint (xs : V → X) :
        (if ∀ s ∈ S, near (xs (u s)) (xs (v s)) then (1 : ℝ) else 0) =
        if A xs then F xs else 0 := by
      have hS' : S = insert t R := (Finset.insert_erase ht).symm
      rw [hS']
      simp only [Finset.forall_mem_insert, F, A]
      split_ifs <;> simp_all
    have hfirst := Lane_sol_s15_transfer.E_pi_charge_one (fun _ : V => P) (u t) F A p
      (fun xs => by dsimp [F]; split_ifs <;> norm_num) hskip hcharge
    have hrest : (FinLaw.pi (fun _ : V => P)).E F ≤ p ^ R.card := by
      have h := ih R hRss (fun a ha b hb => hu (hRsub ha) (hRsub hb)) (fun s hs => hr s (hRsub hs))
      convert h using 1
      unfold FinLaw.E FinLaw.pr
      apply Finset.sum_congr rfl
      intro xs hxs
      dsimp [F]
      by_cases hcond : ∀ t ∈ R, near (xs (u t)) (xs (v t))
      · simp only [if_pos hcond, mul_one]
      · simp only [if_neg hcond, mul_zero]
    calc
      _ = (FinLaw.pi (fun _ : V => P)).E (fun xs => if A xs then F xs else 0) := by
        rw [Lane_sol_s15_transfer.pr_eq_E_indicator]
        congr 1
        funext xs
        have h := hpoint xs
        by_cases hxs : ∀ s ∈ S, near (xs (u s)) (xs (v s))
        · simpa only [if_pos hxs] using h
        · simpa only [if_neg hxs] using h
      _ ≤ p * (FinLaw.pi (fun _ : V => P)).E F := hfirst
      _ ≤ p * p ^ R.card := mul_le_mul_of_nonneg_left hrest hp
      _ = p ^ S.card := by
        have hcard : S.card = R.card + 1 := by
          have hpos := Finset.card_pos.mpr ⟨t, ht⟩
          dsimp [R]
          rw [Finset.card_erase_of_mem ht]
          omega
        rw [hcard, pow_succ]; ring
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [FinLaw.pr, P.sum_one, FinLaw.sum_one]

noncomputable def graphRoot {n : ℕ} (E : SimpleGraph (Fin n)) (v : Fin n) : Fin n :=
  (Finset.univ.filter fun w => E.Reachable v w).min' (by
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl v⟩⟩)

theorem graphRoot_reachable {n : ℕ} (E : SimpleGraph (Fin n)) (v : Fin n) :
    E.Reachable v (graphRoot E v) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

theorem graphRoot_le {n : ℕ} (E : SimpleGraph (Fin n)) (v w : Fin n)
    (h : E.Reachable v w) : graphRoot E v ≤ w :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem graphRoot_eq_of_reachable {n : ℕ} (E : SimpleGraph (Fin n)) {v w : Fin n}
    (h : E.Reachable v w) : graphRoot E v = graphRoot E w := by
  apply le_antisymm
  · exact graphRoot_le E v _ (h.trans (graphRoot_reachable E w))
  · exact graphRoot_le E w _ (h.symm.trans (graphRoot_reachable E v))

theorem graphRoot_eq_iff {n : ℕ} (E : SimpleGraph (Fin n)) (v : Fin n) :
    graphRoot E v = v ↔ ∀ w, E.Reachable w v → v ≤ w := by
  constructor
  · intro h w hw
    rw [← h]
    exact graphRoot_le E v w hw.symm
  · intro h
    exact le_antisymm (graphRoot_le E v v (.refl v)) (h _ (graphRoot_reachable E v).symm)

theorem graph_parent_exists {n : ℕ} (E : SimpleGraph (Fin n)) (v : Fin n)
    (hv : graphRoot E v ≠ v) :
    ∃ w, E.Adj v w ∧ E.dist w (graphRoot E w) < E.dist v (graphRoot E v) := by
  obtain ⟨p, hp⟩ := (graphRoot_reachable E v).exists_walk_length_eq_dist
  generalize hz : graphRoot E v = z at p hp
  cases p with
  | nil => exact (hv hz).elim
  | @cons _ w _ hadj q =>
    refine ⟨w, hadj, ?_⟩
    have hroot : graphRoot E w = graphRoot E v := (graphRoot_eq_of_reachable E hadj.reachable).symm
    rw [hroot, hz]
    have hdist : E.dist w z ≤ q.length := SimpleGraph.dist_le q
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

theorem graph_rank_witness {n j : ℕ} (E : SimpleGraph (Fin n))
    (hj : j ≤ n - (Finset.univ.filter fun v => ∀ w, E.Reachable w v → v ≤ w).card) :
    ∃ u v : Fin j → Fin n, Function.Injective u ∧
      (∀ t, E.Adj (u t) (v t)) ∧
      ∃ r : Fin n → ℕ, ∀ t, r (v t) < r (u t) := by
  let U := {v : Fin n // graphRoot E v ≠ v}
  have hUcard : Fintype.card U = n -
      (Finset.univ.filter fun v => ∀ w, E.Reachable w v → v ≤ w).card := by
    dsimp [U]
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    congr 1
    exact Fintype.card_of_subtype _ (fun v => by simp [graphRoot_eq_iff])
  have hcard : Fintype.card (Fin j) ≤ Fintype.card U := by simpa [hUcard] using hj
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let u : Fin j → Fin n := fun t => (e t).1
  let v : Fin j → Fin n := fun t => Classical.choose (graph_parent_exists E (u t) (e t).2)
  refine ⟨u, v, ?_, ?_, fun w => E.dist w (graphRoot E w), ?_⟩
  · intro t s h
    exact e.injective (Subtype.ext h)
  · intro t
    exact (Classical.choose_spec (graph_parent_exists E (u t) (e t).2)).1
  · intro t
    exact (Classical.choose_spec (graph_parent_exists E (u t) (e t).2)).2

theorem rank_probability_le {X : Type*} [Fintype X] {n j : ℕ}
    (P : FinLaw X) (near : X → X → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hnear : ∀ y, P.pr (fun x => near x y) ≤ p)
    (E : (Fin n → X) → SimpleGraph (Fin n))
    (hE : ∀ xs u v, (E xs).Adj u v → near (xs u) (xs v)) :
    (FinLaw.pi (fun _ : Fin n => P)).pr (fun xs =>
      j ≤ n - (Finset.univ.filter fun v => ∀ w, (E xs).Reachable w v → v ≤ w).card) ≤
      ((n : ℝ) ^ 2 * p) ^ j := by
  let W := (Fin j → Fin n) × (Fin j → Fin n)
  let good : W → Prop := fun w => Function.Injective w.1 ∧
    ∃ r : Fin n → ℕ, ∀ t, r (w.2 t) < r (w.1 t)
  let A : W → (Fin n → X) → Prop := fun w xs =>
    good w ∧ ∀ t, near (xs (w.1 t)) (xs (w.2 t))
  let Q := FinLaw.pi (fun _ : Fin n => P)
  have hcover (xs : Fin n → X) (hxs :
      j ≤ n - (Finset.univ.filter fun v => ∀ w, (E xs).Reachable w v → v ≤ w).card) :
      ∃ w ∈ (Finset.univ : Finset W), A w xs := by
    obtain ⟨u, v, hu, huv, hr⟩ := graph_rank_witness (E xs) hxs
    exact ⟨⟨u, v⟩, Finset.mem_univ _, ⟨hu, hr⟩, fun t => hE xs _ _ (huv t)⟩
  have hcost (w : W) : Q.pr (A w) ≤ p ^ j := by
    by_cases hgood : good w
    · obtain ⟨hu, r, hr⟩ := hgood
      have hgood' : good w := ⟨hu, r, hr⟩
      have h := forest_probability_le P near p hp hnear w.1 w.2 r Finset.univ
        (fun a _ b _ h => hu h) (fun t _ => hr t)
      simpa only [Q, A, hgood', true_and, Finset.mem_univ, forall_const,
        Finset.card_univ, Fintype.card_fin] using h
    · have hzero : Q.pr (A w) = 0 := by simp [FinLaw.pr, A, hgood]
      rw [hzero]; positivity
  calc
    _ ≤ Q.pr (fun xs => ∃ w ∈ (Finset.univ : Finset W), A w xs) := by
      unfold FinLaw.pr
      apply Finset.sum_le_sum
      intro xs hxs
      by_cases h : j ≤ n - (Finset.univ.filter fun v => ∀ w, (E xs).Reachable w v → v ≤ w).card
      · rw [if_pos h, if_pos (hcover xs h)]
      · rw [if_neg h]; split_ifs <;> simp [Q.nonneg xs]
    _ ≤ ∑ w : W, Q.pr (A w) := by
      exact Lane_sol_s15_transfer.pr_finset_exists_le_sum Q Finset.univ A
    _ ≤ ∑ _w : W, p ^ j := Finset.sum_le_sum fun w _ => hcost w
    _ = ((n : ℝ) ^ 2 * p) ^ j := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, W,
        Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      rw [mul_pow, pow_two]
      ring

noncomputable def crossingGraph {κ : CConsts} {T : Stage} {k : ℕ}
    (PT : ProfiledTiling κ T k) (vs : Fin (T.S.n k) → EvenPosition T k)
    (G : Finset (Fin (T.S.n k))) : SimpleGraph (Fin (T.S.n k)) where
  Adj := clusterCrossingEdge PT vs G
  symm := ⟨by
    intro r t h
    refine ⟨h.2.1, h.1, Ne.symm h.2.2.1, ?_⟩
    simpa [clusterCrossingNear, _root_.hammingDist_comm] using h.2.2.2⟩
  loopless := ⟨by intro r h; exact h.2.2.1 rfl⟩

end HypercubeRamsey.Lane_sol_s15_c2
