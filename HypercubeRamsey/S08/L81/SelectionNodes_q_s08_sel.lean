import HypercubeRamsey.S08.L81.Experiment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace HypercubeRamsey.Lane_q_s08_sel

open HypercubeRamsey.S08
open Classical OAI.HypercubeRamsey
variable {η₀ β p : ℝ} {h : ℕ}

private theorem finProb_ext {Ω : Type*} [Fintype Ω] {P Q : FinProb Ω}
    (hw : P.w = Q.w) : P = Q := by
  cases P with
  | mk w₁ hw₁ hs₁ =>
    cases Q with
    | mk w₂ hw₂ hs₂ =>
      simp only at hw
      subst w₂
      rfl

theorem pr_exists_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (Q : FinProb Ω) (Bad : I → Ω → Prop) :
    Q.pr (fun ω => ∃ i, Bad i ω) ≤ ∑ i, Q.pr (Bad i) := by
  classical
  letI : DecidablePred (fun ω : Ω => ∃ i, Bad i ω) := fun ω => Classical.propDecidable _
  letI : ∀ i, DecidablePred (Bad i) := fun i ω => Classical.propDecidable _
  unfold FinProb.pr
  calc
    (∑ ω, if ∃ i, Bad i ω then Q.w ω else 0) ≤
        ∑ ω, ∑ i, if Bad i ω then Q.w ω else 0 := by
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hbad : ∃ i, Bad i ω
      · rcases hbad with ⟨i, hi⟩
        have hex : ∃ i, Bad i ω := ⟨i, hi⟩
        have hsingle : Q.w ω ≤ ∑ i, if Bad i ω then Q.w ω else 0 := by
          have hsingle := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun j => if Bad j ω then Q.w ω else 0)
            (fun j hj => by
              by_cases h : Bad j ω
              · simpa [h] using Q.nonneg ω
              · simp [h])
            (Finset.mem_univ i)
          simpa [hi] using hsingle
        simpa [hex] using hsingle
      · have hsum : 0 ≤ ∑ i, if Bad i ω then Q.w ω else 0 :=
          Finset.sum_nonneg fun i _ => by
            by_cases h : Bad i ω
            · simpa [h] using Q.nonneg ω
            · simp [h]
        simpa [hbad] using hsum
    _ = ∑ i, ∑ ω, if Bad i ω then Q.w ω else 0 := by rw [Finset.sum_comm]

private theorem hammingBall_card_le_sum_choose {d R : ℕ} (v : CubeVertex d) :
    (hammingBall v R).card ≤ ∑ j ∈ Finset.range (R + 1), Nat.choose d j := by
  classical
  let support : CubeVertex d → Finset (Fin d) := fun u =>
    Finset.univ.filter (fun i => u i ≠ v i)
  let B := hammingBall v R
  let Q := (Finset.univ : Finset (Fin d)).powerset.filter (fun s => s.card ≤ R)
  have hsupportDist (u : CubeVertex d) : (support u).card = hammingDist v u := by
    simp [support, hammingDist, ne_comm]
  have hinj : Set.InjOn support (B : Set (CubeVertex d)) := by
    intro x hx y hy hxy
    funext i
    have hiff : x i ≠ v i ↔ y i ≠ v i := by
      have h := congrArg (fun s : Finset (Fin d) => i ∈ s) hxy
      simpa [support] using h
    cases hv : v i <;> cases hxv : x i <;> cases hyv : y i <;> simp_all
  have hsubset : B.image support ⊆ Q := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨u, hu, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    have hu' : u ∈ hammingBall v R := by simpa [B] using hu
    have hdistle : hammingDist v u ≤ R := (Finset.mem_filter.mp hu').2
    rw [hsupportDist]
    exact hdistle
  have hcard : B.card ≤ Q.card := by
    calc
      B.card = (B.image support).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ Q.card := Finset.card_le_card hsubset
  have hQsum : Q.card =
      ∑ k ∈ Finset.range (d + 1), if k ≤ R then Nat.choose d k else 0 := by
    calc
      Q.card = ∑ s ∈ (Finset.univ : Finset (Fin d)).powerset,
          if s.card ≤ R then 1 else 0 := by
        simpa [Q] using (Finset.natCast_card_filter
          (p := fun s : Finset (Fin d) => s.card ≤ R)
          (s := (Finset.univ : Finset (Fin d)).powerset))
      _ = ∑ k ∈ Finset.range (d + 1),
          Nat.choose d k * (if k ≤ R then 1 else 0) := by
        simpa [Fintype.card_fin, nsmul_eq_mul] using
          (Finset.sum_powerset_apply_card
            (f := fun k : ℕ => if k ≤ R then (1 : ℕ) else 0)
            (x := (Finset.univ : Finset (Fin d))))
      _ = _ := by simp
  let S := (Finset.range (d + 1)).filter (fun j => j ≤ R)
  have hQtoS : Q.card = ∑ j ∈ S, Nat.choose d j := by
    rw [hQsum]
    simp [S, Finset.sum_filter]
  have hSsub : S ⊆ Finset.range (R + 1) := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj')
  have hsum : (∑ j ∈ S, Nat.choose d j) ≤
      ∑ j ∈ Finset.range (R + 1), Nat.choose d j :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub (by intros; exact Nat.zero_le _)
  calc
    (hammingBall v R).card = B.card := rfl
    _ ≤ Q.card := hcard
    _ = ∑ j ∈ S, Nat.choose d j := hQtoS
    _ ≤ ∑ j ∈ Finset.range (R + 1), Nat.choose d j := hsum

theorem small_powerset_card {α : Type*} [DecidableEq α] (U : Finset α) (T : ℕ) :
    (U.powerset.filter fun S => S.card ≤ T).card ≤ (U.card + 1) ^ (T + 1) := by
  classical
  let Q := U.powerset.filter fun S => S.card ≤ T
  have hcount : Q.card =
      ∑ k ∈ Finset.range (U.card + 1),
        if k ≤ T then Nat.choose U.card k else 0 := by
    calc
      Q.card = ∑ S ∈ U.powerset, if S.card ≤ T then 1 else 0 := by
        simpa [Q] using (Finset.natCast_card_filter
          (p := fun S : Finset α => S.card ≤ T) (s := U.powerset))
      _ = ∑ k ∈ Finset.range (U.card + 1),
          Nat.choose U.card k * (if k ≤ T then 1 else 0) := by
        simpa [Fintype.card_fin, nsmul_eq_mul] using
          (Finset.sum_powerset_apply_card
            (f := fun k : ℕ => if k ≤ T then (1 : ℕ) else 0) (x := U))
      _ = _ := by simp
  have hbase : 1 ≤ U.card + 1 := by omega
  have hterm (k : ℕ) : (if k ≤ T then Nat.choose U.card k else 0) ≤
      (U.card + 1) ^ T := by
    by_cases hk : k ≤ T
    · simp [hk]
      calc
        Nat.choose U.card k ≤ U.card ^ k := Nat.choose_le_pow _ _
        _ ≤ (U.card + 1) ^ k := Nat.pow_le_pow_left (by omega) _
        _ ≤ (U.card + 1) ^ T := Nat.pow_le_pow_right (by omega) hk
    · simp [hk]
  calc
    Q.card ≤ ∑ k ∈ Finset.range (U.card + 1), (U.card + 1) ^ T := by
      rw [hcount]
      exact Finset.sum_le_sum fun k hk => hterm k
    _ = (U.card + 1) * (U.card + 1) ^ T := by simp [Finset.sum_const, nsmul_eq_mul]
    _ = (U.card + 1) ^ (T + 1) := by rw [pow_succ]; ring

theorem ordNbrs_card_bound {η₀ : ℝ} {n : ℕ} (a : Res η₀ n) :
    (ordNbrs a).card ≤ dC η₀ n + 1 := by
  have hball : ordNbrs a = hammingBall a 1 := by
    ext b
    simp [ordNbrs, hammingBall, HypercubeRamsey.hammingDist, _root_.hammingDist]
  calc
    (ordNbrs a).card = (hammingBall a 1).card := by rw [hball]
    _ ≤ ∑ j ∈ Finset.range (1 + 1), Nat.choose (dC η₀ n) j :=
      hammingBall_card_le_sum_choose (d := dC η₀ n) (R := 1) a
    _ = Nat.choose (dC η₀ n) 0 + Nat.choose (dC η₀ n) 1 := by
      simp [Finset.sum_range_succ, Nat.choose_zero_right, Nat.choose_one_right]
    _ = dC η₀ n + 1 := by simp [Nat.choose_zero_right, Nat.choose_one_right]; omega

private theorem foldl_mem_or {α : Type*} (step : List α → α → List α)
    (hstep : ∀ acc a x, x ∈ step acc a → x ∈ acc ∨ x = a) :
    ∀ (l : List α) (acc : List α) (x : α),
      x ∈ l.foldl step acc → x ∈ acc ∨ x ∈ l := by
  intro l
  induction l with
  | nil =>
      intro acc x hx
      exact Or.inl (by simpa using hx)
  | cons a l ih =>
      intro acc x hx
      rw [List.foldl_cons] at hx
      rcases ih (step acc a) x hx with hmem | htail
      · rcases hstep acc a x hmem with hacc | rfl
        · exact Or.inl hacc
        · exact Or.inr (by simp)
      · exact Or.inr (by simp [htail])

private theorem greedy_mem_source {α β : Type*}
    (ids : α → Finset β) (l : List α) {x : α} (hx : x ∈ greedy ids l) : x ∈ l := by
  classical
  unfold greedy at hx
  have hstep : ∀ acc a y,
      y ∈ (fun acc L => if Disjoint (ids L)
        (acc.foldr (fun L' s => ids L' ∪ s) ∅) then acc ++ [L] else acc) acc a →
        y ∈ acc ∨ y = a := by
    intro acc a y hy
    by_cases hd : Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅)
    · have hy' : y ∈ acc ++ [a] := by simpa [hd] using hy
      rcases List.mem_append.mp hy' with hyacc | hyone
      · exact Or.inl hyacc
      · exact Or.inr (List.mem_singleton.mp hyone)
    · exact Or.inl (by simpa [hd] using hy)
  rcases foldl_mem_or
      (fun acc L => if Disjoint (ids L)
        (acc.foldr (fun L' s => ids L' ∪ s) ∅) then acc ++ [L] else acc)
      hstep l [] x hx with hnil | hmem
  · simpa using hnil
  · exact hmem

theorem family_candidate (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos)
    (t : D.Tags) (c : D.CellT) {L : D.LList c.1} (hL : L ∈ D.family Θ P t c) :
    D.Cand P c L := by
  have hsrc := greedy_mem_source (D.listIds c.1)
    ((D.listOrder c.1).filter fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L)) hL
  have hfilter : L ∈ (D.listOrder c.1).filter
      (fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L)) := by
    simpa [Ctx.family] using hsrc
  rcases List.mem_filter.mp hfilter with ⟨_, hdec⟩
  exact (of_decide_eq_true hdec).1

theorem family_badList (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos)
    (t : D.Tags) (c : D.CellT) {L : D.LList c.1} (hL : L ∈ D.family Θ P t c) :
    D.BadList Θ t c L := by
  have hsrc := greedy_mem_source (D.listIds c.1)
    ((D.listOrder c.1).filter fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L)) hL
  have hfilter : L ∈ (D.listOrder c.1).filter
      (fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L)) := by
    simpa [Ctx.family] using hsrc
  rcases List.mem_filter.mp hfilter with ⟨_, hdec⟩
  exact (of_decide_eq_true hdec).2

private noncomputable def greedyIdUnion {α β : Type*} (ids : α → Finset β) (acc : List α) : Finset β :=
  acc.foldr (fun a s => ids a ∪ s) ∅

private theorem mem_greedyIdUnion_iff {α β : Type*}
    (ids : α → Finset β) (acc : List α) (x : β) :
    x ∈ greedyIdUnion ids acc ↔ ∃ a ∈ acc, x ∈ ids a := by
  classical
  induction acc with
  | nil => simp [greedyIdUnion]
  | cons a acc ih =>
      simp only [greedyIdUnion, List.foldr_cons, Finset.mem_union]
      change (x ∈ ids a ∨ x ∈ greedyIdUnion ids acc) ↔ _
      rw [ih]
      simp [List.mem_cons]

private noncomputable def greedyStep {α β : Type*} (ids : α → Finset β) (acc : List α) (a : α) : List α :=
  if Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) then acc ++ [a] else acc

private theorem mem_greedyStep_of_mem {α β : Type*} (ids : α → Finset β)
    (acc : List α) (a x : α) (hx : x ∈ acc) : x ∈ greedyStep ids acc a := by
  classical
  by_cases h : Disjoint (ids a) (greedyIdUnion ids acc)
  · have h' : Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) := by
      simpa [greedyIdUnion] using h
    simp [greedyStep, h', hx]
  · have h' : ¬ Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) := by
      simpa [greedyIdUnion] using h
    simp [greedyStep, h', hx]

private theorem mem_foldl_greedyStep_of_mem {α β : Type*} (ids : α → Finset β) :
    ∀ (l : List α) (acc : List α) (x : α), x ∈ acc →
      x ∈ l.foldl (greedyStep ids) acc := by
  classical
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      intro acc x hx
      rw [List.foldl_cons]
      exact ih (greedyStep ids acc a) x (mem_greedyStep_of_mem ids acc a x hx)

private theorem greedy_collision_of_failed_step {α β : Type*}
    (ids : α → Finset β) (acc : List α) (a : α)
    (h : ¬ Disjoint (ids a) (greedyIdUnion ids acc)) :
    ∃ b ∈ acc, ¬ Disjoint (ids a) (ids b) := by
  classical
  obtain ⟨x, hxA, hxUnion⟩ := Finset.not_disjoint_iff.mp h
  obtain ⟨b, hb, hxb⟩ := (mem_greedyIdUnion_iff ids acc x).mp hxUnion
  exact ⟨b, hb, Finset.not_disjoint_iff.mpr ⟨x, hxA, hxb⟩⟩

private theorem foldl_greedyStep_source_hit_aux {α β : Type*}
    (ids : α → Finset β) :
    ∀ (l : List α) (acc : List α) (a : α), a ∈ l →
      a ∈ l.foldl (greedyStep ids) acc ∨
        ∃ b ∈ l.foldl (greedyStep ids) acc, ¬ Disjoint (ids a) (ids b) := by
  classical
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro acc a ha
      rcases List.mem_cons.mp ha with hxa | haxs
      · subst a
        by_cases hdis : Disjoint (ids x) (greedyIdUnion ids acc)
        · left
          have hdis' : Disjoint (ids x) (acc.foldr (fun L' s => ids L' ∪ s) ∅) := by
            simpa [greedyIdUnion] using hdis
          have hx : x ∈ greedyStep ids acc x := by
            simp [greedyStep, hdis']
          exact mem_foldl_greedyStep_of_mem ids xs (greedyStep ids acc x) x hx
        · right
          obtain ⟨b, hb, hhit⟩ := greedy_collision_of_failed_step ids acc x hdis
          exact ⟨b, mem_foldl_greedyStep_of_mem ids xs (greedyStep ids acc x) b
            (mem_greedyStep_of_mem ids acc x b hb), hhit⟩
      · simpa only [List.foldl_cons] using ih (greedyStep ids acc x) a haxs

private theorem greedy_eq_foldl_greedyStep {α β : Type*}
    (ids : α → Finset β) (l : List α) : greedy ids l = l.foldl (greedyStep ids) [] := by
  classical
  unfold greedy
  change l.foldl (fun acc a =>
    if Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) then acc ++ [a] else acc) [] =
    l.foldl (greedyStep ids) []
  have hs : (fun acc a =>
      if Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) then acc ++ [a] else acc) =
      greedyStep ids := by
    funext acc a
    rfl
  rw [hs]

private theorem greedyStep_pairwise {α β : Type*}
    (ids : α → Finset β) (acc : List α) (a : α)
    (hacc : acc.Pairwise fun x y => Disjoint (ids x) (ids y)) :
    (greedyStep ids acc a).Pairwise fun x y => Disjoint (ids x) (ids y) := by
  classical
  by_cases h : Disjoint (ids a) (greedyIdUnion ids acc)
  · have h' : Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) := by
      simpa [greedyIdUnion] using h
    have hcross : ∀ x ∈ acc, Disjoint (ids x) (ids a) := by
      intro x hx
      apply Finset.disjoint_left.mpr
      intro z hzX hzA
      have hzUnion : z ∈ greedyIdUnion ids acc :=
        (mem_greedyIdUnion_iff ids acc z).mpr ⟨x, hx, hzX⟩
      exact (Finset.disjoint_left.mp h) hzA (by simpa [greedyIdUnion] using hzUnion)
    have hstep : greedyStep ids acc a = acc ++ [a] := by
      simp [greedyStep, h']
    rw [hstep, List.pairwise_append]
    refine ⟨hacc, ?_, ?_⟩
    · simp
    · intro x hx y hy
      simp at hy
      subst y
      exact hcross x hx
  · have h' : ¬ Disjoint (ids a) (acc.foldr (fun L' s => ids L' ∪ s) ∅) := by
      simpa [greedyIdUnion] using h
    simpa [greedyStep, h'] using hacc

private theorem foldl_greedyStep_pairwise {α β : Type*} (ids : α → Finset β) :
    ∀ (l acc : List α), acc.Pairwise (fun x y => Disjoint (ids x) (ids y)) →
      (l.foldl (greedyStep ids) acc).Pairwise (fun x y => Disjoint (ids x) (ids y)) := by
  classical
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
      intro acc hacc
      rw [List.foldl_cons]
      exact ih (greedyStep ids acc a) (greedyStep_pairwise ids acc a hacc)

theorem greedy_pairwise_disjoint {α β : Type*} (ids : α → Finset β) (l : List α) :
    (greedy ids l).Pairwise (fun x y => Disjoint (ids x) (ids y)) := by
  classical
  rw [greedy_eq_foldl_greedyStep ids l]
  exact foldl_greedyStep_pairwise ids l [] (by simp)

theorem greedy_mem_or_overlap {α β : Type*}
    (ids : α → Finset β) (l : List α) {a : α} (ha : a ∈ l) :
    a ∈ greedy ids l ∨ ∃ b ∈ greedy ids l, ¬ Disjoint (ids a) (ids b) := by
  classical
  have hEq := greedy_eq_foldl_greedyStep ids l
  rw [hEq]
  exact foldl_greedyStep_source_hit_aux ids l [] a ha

theorem family_pairwise_disjoint (D : Ctx η₀ β p h) (Θ : D.Hist) (P : D.Pos)
    (t : D.Tags) (c : D.CellT) :
    (D.family Θ P t c).Pairwise
      (fun L L' => Disjoint (D.listIds c.1 L) (D.listIds c.1 L')) := by
  classical
  unfold Ctx.family
  exact greedy_pairwise_disjoint (D.listIds c.1)
    ((D.listOrder c.1).filter fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L))

theorem listIds_card_bound (D : Ctx η₀ β p h) (g : D.KeyT) (L : D.LList g) :
    (D.listIds g L).card ≤ L.1.card + (crossKeys g).card := by
  classical
  unfold Ctx.listIds
  calc
    (L.1.image (fun ℓ => (g, ℓ)) ∪
        Finset.univ.image (fun u : D.CrossSub g => (u.1, L.2 u))).card ≤
      (L.1.image (fun ℓ => (g, ℓ))).card +
        (Finset.univ.image (fun u : D.CrossSub g => (u.1, L.2 u))).card :=
      Finset.card_union_le _ _
    _ ≤ L.1.card + Fintype.card (D.CrossSub g) :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = L.1.card + (crossKeys g).card := by simp [Ctx.CrossSub]

noncomputable def localIdsAt (D : Ctx η₀ β p h) (P : D.Pos) (g : D.KeyT)
    (b : D.ResT) (j : Fin (HH η₀ D.n + 1)) : Finset D.Loc :=
  (Finset.univ.filter fun u : D.ResT =>
    P g (u, j) = true ∧ _root_.hammingDist u b ≤ rH D.n).image (fun u => (u, j))

theorem localIdsAt_card (D : Ctx η₀ β p h) (P : D.Pos) (g : D.KeyT)
    (b : D.ResT) (j : Fin (HH η₀ D.n + 1)) :
    (localIdsAt D P g b j).card = D.ballCount P g b j := by
  classical
  have hinj : Function.Injective (fun u : D.ResT => (u, j)) := by
    intro u v h
    exact congrArg Prod.fst h
  simp [localIdsAt, Ctx.ballCount, Finset.card_image_of_injective _ hinj]

private theorem keyDist_triangle {η₀ : ℝ} {n : ℕ} (a b c : Key η₀ n) :
    keyDist a c ≤ keyDist a b + keyDist b c := by
  unfold keyDist
  calc
    (∑ r, Nat.dist (a r).val (c r).val) ≤
        ∑ r, (Nat.dist (a r).val (b r).val + Nat.dist (b r).val (c r).val) :=
      Finset.sum_le_sum fun r _ => Nat.dist.triangle_inequality _ _ _
    _ = (∑ r, Nat.dist (a r).val (b r).val) +
        ∑ r, Nat.dist (b r).val (c r).val := Finset.sum_add_distrib

theorem keyDist_symm {η₀ : ℝ} {n : ℕ} (a b : Key η₀ n) :
    keyDist a b = keyDist b a := by
  unfold keyDist
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.dist_comm _ _

private theorem crossKey_dist_le_one {η₀ : ℝ} {n : ℕ} {g u : Key η₀ n}
    (hu : u ∈ crossKeys g) : keyDist g u ≤ 1 := by
  have hu' : keyDist g u = 1 := by simpa [crossKeys] using hu
  omega

private theorem padNbr_cell_dist {η₀ : ℝ} {n : ℕ} {c e : Cell η₀ n}
    (he : PadNbr c e) : keyDist c.1 e.1 ≤ 1 ∧ _root_.hammingDist c.2 e.2 ≤ 1 := by
  rcases he with ⟨hkey, hres⟩ | ⟨hres, hkey⟩
  · constructor
    · rw [hkey]
      simp [keyDist]
    · simpa [ordNbrs] using hres
  · constructor
    have hdist := crossKey_dist_le_one hkey
    · exact hdist
    · rw [hres]
      simp

private theorem padNbr_cell_key_in_ball {η₀ : ℝ} {n : ℕ} {g : Key η₀ n}
    {b : Res η₀ n} {c : Cell η₀ n} (he : PadNbr c (g, b)) :
    c.1 ∈ keyBall g 2 := by
  have hdist := (padNbr_cell_dist he).1
  have hsymm : keyDist g c.1 ≤ 1 := by
    rw [keyDist_symm]
    exact hdist
  simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private theorem cross_of_padNbr_key_in_ball {η₀ : ℝ} {n : ℕ} {g : Key η₀ n}
    {b : Res η₀ n} {c : Cell η₀ n} (he : PadNbr c (g, b))
    (u : {u : Key η₀ n // u ∈ crossKeys c.1}) : u.1 ∈ keyBall g 2 := by
  have hc := (padNbr_cell_dist he).1
  have hcg : keyDist g c.1 ≤ 1 := by
    rw [keyDist_symm]
    exact hc
  have hcu := crossKey_dist_le_one u.2
  have hdist := (keyDist_triangle g c.1 u.1).trans (Nat.add_le_add hcg hcu)
  simp [keyBall]
  omega

private theorem cand_internal_radius (D : Ctx η₀ β p h) (P : D.Pos)
    {c e : D.CellT} (he : PadNbr c e) {L : D.LList c.1}
    (hL : D.Cand P c L) {ℓ : D.Loc} (hℓ : ℓ ∈ L.1) :
    _root_.hammingDist ℓ.1 e.2 ≤ rH D.n + 2 := by
  obtain ⟨b, hb, hℓb⟩ := (hL.2.1 ℓ hℓ).2
  have hcb : _root_.hammingDist c.2 b ≤ 1 := by
    simpa [ordNbrs] using hb
  have hbc : _root_.hammingDist b c.2 ≤ 1 := by
    rw [_root_.hammingDist_comm]
    exact hcb
  have hce := (padNbr_cell_dist he).2
  have hdist₁ := _root_.hammingDist_triangle ℓ.1 b e.2
  have hdist₂ := _root_.hammingDist_triangle b c.2 e.2
  omega

private theorem cand_cross_radius (D : Ctx η₀ β p h) (P : D.Pos)
    {c e : D.CellT} (he : PadNbr c e) {L : D.LList c.1}
    (hL : D.Cand P c L) (u : D.CrossSub c.1) :
    _root_.hammingDist (L.2 u).1 e.2 ≤ rH D.n + 2 := by
  have hℓ := (hL.2.2 u).2
  have hce := (padNbr_cell_dist he).2
  have hdist := _root_.hammingDist_triangle (L.2 u).1 c.2 e.2
  omega

private theorem cand_eq_of_local_pos_agree (D : Ctx η₀ β p h)
    (P P' : D.Pos) (g : D.KeyT) (b b₀ : D.ResT)
    (hsite : _root_.hammingDist b b₀ ≤ 4 * HH η₀ D.n)
    (hP : ∀ k ∈ keyBall g 2, ∀ ℓ : D.Loc,
      _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 → P k ℓ = P' k ℓ)
    (c : D.CellT) (hPad : PadNbr c (g, b)) (L : D.LList c.1) :
    D.Cand P c L ↔ D.Cand P' c L := by
  constructor
  · intro hL
    rcases hL with ⟨hcard, hint, hcross⟩
    have hwhole : D.Cand P c L := ⟨hcard, hint, hcross⟩
    have hcKey : c.1 ∈ keyBall g 2 := padNbr_cell_key_in_ball hPad
    refine ⟨hcard, ?_, ?_⟩
    · intro ℓ hℓ
      rcases hint ℓ hℓ with ⟨hp, hnear⟩
      have hbound : _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
        have hrad := cand_internal_radius D P hPad hwhole hℓ
        have hrad' : _root_.hammingDist ℓ.1 b ≤ rH D.n + 2 := by simpa using hrad
        have htri := _root_.hammingDist_triangle ℓ.1 b b₀
        omega
      have heq := hP c.1 hcKey ℓ hbound
      exact ⟨by rw [← heq]; exact hp, hnear⟩
    · intro u
      rcases hcross u with ⟨hp, hnear⟩
      have hbound : _root_.hammingDist (L.2 u).1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
        have hrad := cand_cross_radius D P hPad hwhole u
        have hrad' : _root_.hammingDist (L.2 u).1 b ≤ rH D.n + 2 := by simpa using hrad
        have htri := _root_.hammingDist_triangle (L.2 u).1 b b₀
        omega
      have huKey : u.1 ∈ keyBall g 2 := cross_of_padNbr_key_in_ball hPad u
      have heq := hP u.1 huKey (L.2 u) hbound
      exact ⟨by rw [← heq]; exact hp, hnear⟩
  · intro hL
    rcases hL with ⟨hcard, hint, hcross⟩
    have hwhole : D.Cand P' c L := ⟨hcard, hint, hcross⟩
    have hcKey : c.1 ∈ keyBall g 2 := padNbr_cell_key_in_ball hPad
    refine ⟨hcard, ?_, ?_⟩
    · intro ℓ hℓ
      rcases hint ℓ hℓ with ⟨hp, hnear⟩
      have hbound : _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
        have hrad := cand_internal_radius D P' hPad hwhole hℓ
        have hrad' : _root_.hammingDist ℓ.1 b ≤ rH D.n + 2 := by simpa using hrad
        have htri := _root_.hammingDist_triangle ℓ.1 b b₀
        omega
      have heq := hP c.1 hcKey ℓ hbound
      exact ⟨by rw [heq]; exact hp, hnear⟩
    · intro u
      rcases hcross u with ⟨hp, hnear⟩
      have hbound : _root_.hammingDist (L.2 u).1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
        have hrad := cand_cross_radius D P' hPad hwhole u
        have hrad' : _root_.hammingDist (L.2 u).1 b ≤ rH D.n + 2 := by simpa using hrad
        have htri := _root_.hammingDist_triangle (L.2 u).1 b b₀
        omega
      have huKey : u.1 ∈ keyBall g 2 := cross_of_padNbr_key_in_ball hPad u
      have heq := hP u.1 huKey (L.2 u) hbound
      exact ⟨by rw [heq]; exact hp, hnear⟩

private theorem hist_agree_at_padNbr (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (b : D.ResT) (c : D.CellT)
    (hPad : PadNbr c (g, b))
    (hΘ : ∀ u ∈ keyBall g 3, Θ u = Θ' u) :
    Θ c.1 = Θ' c.1 ∧
      (∀ u ∈ crossKeys c.1, Θ u = Θ' u) ∧
      (∀ u ∈ crossKeys c.1, ∀ v ∈ crossKeys u, Θ v = Θ' v) := by
  have hgc : keyDist g c.1 ≤ 1 := by
    rw [keyDist_symm]
    exact (padNbr_cell_dist hPad).1
  have h0 : Θ c.1 = Θ' c.1 := by
    apply hΘ
    simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h1 : ∀ u ∈ crossKeys c.1, Θ u = Θ' u := by
    intro u hu
    apply hΘ
    have hcu := crossKey_dist_le_one hu
    have hdist := (keyDist_triangle g c.1 u).trans
      (Nat.add_le_add hgc hcu)
    simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have h2 : ∀ u ∈ crossKeys c.1, ∀ v ∈ crossKeys u, Θ v = Θ' v := by
    intro u hu v hv
    apply hΘ
    have hcu := crossKey_dist_le_one hu
    have huv := crossKey_dist_le_one hv
    have hcv := (keyDist_triangle c.1 u v).trans
      (Nat.add_le_add hcu huv)
    have hdist := (keyDist_triangle g c.1 v).trans
      (Nat.add_le_add hgc hcv)
    simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  exact ⟨h0, h1, h2⟩

private theorem family_eq_of_candidate_bad_eq (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (P P' : D.Pos) (t t' : D.Tags) (c : D.CellT)
    (hCand : ∀ L : D.LList c.1, D.Cand P c L ↔ D.Cand P' c L)
    (hBad : ∀ L : D.LList c.1, D.Cand P c L → D.Cand P' c L →
      (D.BadList Θ t c L ↔ D.BadList Θ' t' c L)) :
    D.family Θ P t c = D.family Θ' P' t' c := by
  classical
  unfold Ctx.family
  have hf : (D.listOrder c.1).filter (fun L => decide (D.Cand P c L ∧ D.BadList Θ t c L)) =
      (D.listOrder c.1).filter (fun L => decide (D.Cand P' c L ∧ D.BadList Θ' t' c L)) := by
    apply List.filter_congr
    intro L hL
    by_cases hc : D.Cand P c L
    · have hc' := (hCand L).mp hc
      simp [hc, hc', hBad L hc hc']
    · have hc' : ¬ D.Cand P' c L := fun hh => hc ((hCand L).mpr hh)
      simp [hc, hc']
  rw [hf]

private theorem forbidden_eq_of_family_eq (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (P P' : D.Pos) (t t' : D.Tags) (e : D.CellT) (ℓ : D.Loc)
    (hfamily : ∀ c : D.CellT, PadNbr c e →
      D.family Θ P t c = D.family Θ' P' t' c) :
    (D.Forbidden Θ P t e ℓ ↔ D.Forbidden Θ' P' t' e ℓ) := by
  constructor
  · rintro ⟨c, hce, L, hL, hid, hdist⟩
    exact ⟨c, hce, L, by rw [← hfamily c hce]; exact hL, hid, hdist⟩
  · rintro ⟨c, hce, L, hL, hid, hdist⟩
    exact ⟨c, hce, L, by rw [hfamily c hce]; exact hL, hid, hdist⟩

private theorem elig_eq_of_forbidden_eq (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (P P' : D.Pos) (t t' : D.Tags) (g : D.KeyT)
    (hP : ∀ b ℓ, _root_.hammingDist ℓ.1 b ≤ rH D.n → P g ℓ = P' g ℓ)
    (hF : ∀ b ℓ, D.Forbidden Θ P t (g, b) ℓ ↔ D.Forbidden Θ' P' t' (g, b) ℓ) :
    D.elig Θ P t g = D.elig Θ' P' t' g := by
  funext b j
  apply Finset.ext
  intro ℓ
  simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hj, hd, hnot⟩
    refine ⟨(hP b ℓ hd).symm ▸ hp, hj, hd, ?_⟩
    intro hf
    exact hnot ((hF b ℓ).mpr hf)
  · rintro ⟨hp, hj, hd, hnot⟩
    refine ⟨(hP b ℓ hd) ▸ hp, hj, hd, ?_⟩
    intro hf
    exact hnot ((hF b ℓ).mp hf)

private theorem elig_site_eq_of_forbidden_eq (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (P P' : D.Pos) (t t' : D.Tags)
    (g : D.KeyT) (b : D.ResT)
    (hP : ∀ ℓ, _root_.hammingDist ℓ.1 b ≤ rH D.n → P g ℓ = P' g ℓ)
    (hF : ∀ ℓ, D.Forbidden Θ P t (g, b) ℓ ↔ D.Forbidden Θ' P' t' (g, b) ℓ) :
    ∀ j, D.elig Θ P t g b j = D.elig Θ' P' t' g b j := by
  intro j
  apply Finset.ext
  intro ℓ
  simp only [Ctx.elig, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hj, hd, hnot⟩
    refine ⟨(hP ℓ hd).symm ▸ hp, hj, hd, ?_⟩
    intro hf
    exact hnot ((hF ℓ).mpr hf)
  · rintro ⟨hp, hj, hd, hnot⟩
    refine ⟨(hP ℓ hd) ▸ hp, hj, hd, ?_⟩
    intro hf
    exact hnot ((hF ℓ).mp hf)

private theorem crossHit_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (x : Fin D.N)
    (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.crossHit Θ g x = D.crossHit Θ' g x := by
  apply propext
  constructor <;> intro hh u hu
  · have h := hh u hu
    rw [hθ u hu] at h
    exact h
  · have h := hh u hu
    rw [← hθ u hu] at h
    exact h

private theorem ownHit_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (x : Fin D.N)
    (h0 : Θ g = Θ' g) (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.ownHit Θ g x = D.ownHit Θ' g x := by
  apply propext
  constructor <;> intro hh
  · rcases hh with ⟨hc, ho⟩
    exact ⟨(crossHit_eq_of_hist_agree D Θ Θ' g x hθ).mp hc, by simpa [h0] using ho⟩
  · rcases hh with ⟨hc, ho⟩
    exact ⟨(crossHit_eq_of_hist_agree D Θ Θ' g x hθ).mpr hc, by simpa [h0] using ho⟩

private theorem dMinus_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.dMinus Θ g = D.dMinus Θ' g := by
  funext i
  unfold Ctx.dMinus
  apply Finset.sum_congr rfl
  intro x hx
  rw [crossHit_eq_of_hist_agree D Θ Θ' g x hθ]

private theorem dPlus_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (h0 : Θ g = Θ' g)
    (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.dPlus Θ g = D.dPlus Θ' g := by
  funext i
  unfold Ctx.dPlus
  apply Finset.sum_congr rfl
  intro x hx
  rw [ownHit_eq_of_hist_agree D Θ Θ' g x h0 hθ]

private theorem dOmit_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g u₀ : D.KeyT) (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.dOmit Θ g u₀ = D.dOmit Θ' g u₀ := by
  funext i
  unfold Ctx.dOmit
  apply Finset.sum_congr rfl
  intro x hx
  have htest :
      (∀ u, u ≠ u₀ → u ∈ crossKeys g → D.hitsAll x (Θ u)) ↔
        (∀ u, u ≠ u₀ → u ∈ crossKeys g → D.hitsAll x (Θ' u)) := by
    constructor <;> intro hh u hne hu
    · rw [← hθ u hu]
      exact hh u hne hu
    · rw [hθ u hu]
      exact hh u hne hu
  simp [htest]

private theorem baseGates_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (h0 : Θ g = Θ' g)
    (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.BaseGates Θ g = D.BaseGates Θ' g := by
  have hminus := dMinus_eq_of_hist_agree D Θ Θ' g hθ
  have hplus := dPlus_eq_of_hist_agree D Θ Θ' g h0 hθ
  have homit (u : D.KeyT) : D.dOmit Θ g u = D.dOmit Θ' g u :=
    dOmit_eq_of_hist_agree D Θ Θ' g u hθ
  have hpost (i : D.M.ι) : D.postW (Θ g) i = D.postW (Θ' g) i := by rw [h0]
  have hopen (i : D.M.ι) : D.GateOpen Θ g i = D.GateOpen Θ' g i := by
    simp [Ctx.GateOpen, hminus, hplus]
  have htilt (i : D.M.ι) : D.tiltW Θ g i = D.tiltW Θ' g i := by
    simp [Ctx.tiltW, hpost i, hminus, hopen i]
  have hzg : D.ZG Θ g = D.ZG Θ' g := by
    unfold Ctx.ZG
    apply Finset.sum_congr rfl
    intro i hi
    exact htilt i
  simp [Ctx.BaseGates, Ctx.Gate1, Ctx.Gate2, Ctx.Gate34,
    hpost, hminus, homit, hzg]

private theorem candGate_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (h0 : Θ g = Θ' g)
    (h1 : ∀ u ∈ crossKeys g, Θ u = Θ' u)
    (h2 : ∀ u ∈ crossKeys g, ∀ v ∈ crossKeys u, Θ v = Θ' v) :
    D.CandGate Θ g = D.CandGate Θ' g := by
  have hg := baseGates_eq_of_hist_agree D Θ Θ' g h0 h1
  have hgu (u : D.KeyT) (hu : u ∈ crossKeys g) :
      D.BaseGates Θ u = D.BaseGates Θ' u := by
    exact baseGates_eq_of_hist_agree D Θ Θ' u (h1 u hu) (h2 u hu)
  unfold Ctx.CandGate
  apply propext
  constructor
  · rintro ⟨hb, hs⟩
    exact ⟨hg.mp hb, fun u hu => (hgu u hu).mp (hs u hu)⟩
  · rintro ⟨hb, hs⟩
    exact ⟨hg.mpr hb, fun u hu => (hgu u hu).mpr (hs u hu)⟩

private theorem anchorU_weight_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (h0 : Θ g = Θ' g)
    (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) (i : D.M.ι) (x : Fin D.N) :
    (D.anchorU Θ g i).w x = (D.anchorU Θ' g i).w x := by
  have hown (x : Fin D.N) := ownHit_eq_of_hist_agree D Θ Θ' g x h0 hθ
  simp [Ctx.anchorU, normOr, hown]

private theorem tiltW_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (h0 : Θ g = Θ' g)
    (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) :
    D.tiltW Θ g = D.tiltW Θ' g := by
  have hminus := dMinus_eq_of_hist_agree D Θ Θ' g hθ
  have hplus := dPlus_eq_of_hist_agree D Θ Θ' g h0 hθ
  funext i
  have hpost : D.postW (Θ g) i = D.postW (Θ' g) i := by rw [h0]
  have hopen : D.GateOpen Θ g i = D.GateOpen Θ' g i := by
    simp [Ctx.GateOpen, hminus, hplus]
  simp [Ctx.tiltW, hpost, hminus, hopen]

set_option maxHeartbeats 1000000 in
private theorem tilt_weight_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (h0 : Θ g = Θ' g)
    (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u) (i : D.M.ι) :
    (D.tilt Θ g).w i = (D.tilt Θ' g).w i := by
  have htw := tiltW_eq_of_hist_agree D Θ Θ' g h0 hθ
  simp [Ctx.tilt, normOr, htw]

set_option maxHeartbeats 1000000 in
private theorem refInt_weight_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u)
    (i : D.M.ι) : (D.refInt Θ g).w i = (D.refInt Θ' g).w i := by
  have hminus := dMinus_eq_of_hist_agree D Θ Θ' g hθ
  simp [Ctx.refInt, normOr, hminus]

set_option maxHeartbeats 1000000 in
private theorem omitHit_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (u g : D.KeyT) (x : Fin D.N)
    (hθ : ∀ v ∈ crossKeys u, Θ v = Θ' v) :
    D.omitHit Θ u g x = D.omitHit Θ' u g x := by
  apply propext
  unfold Ctx.omitHit
  constructor <;> intro hh v hv
  · have h := hh v hv
    rw [← hθ v (Finset.mem_of_mem_erase hv)]
    exact h
  · have h := hh v hv
    rw [hθ v (Finset.mem_of_mem_erase hv)]
    exact h

set_option maxHeartbeats 1000000 in
private theorem refCross_weight_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g u : D.KeyT) (h0 : Θ u = Θ' u)
    (hθ : ∀ v ∈ crossKeys u, Θ v = Θ' v) (i : D.M.ι) (x : Fin D.N) :
    (D.refCross Θ g u).w (i, x) = (D.refCross Θ' g u).w (i, x) := by
  have ho : ∀ y, D.omitHit Θ u g y = D.omitHit Θ' u g y :=
    fun y => omitHit_eq_of_hist_agree D Θ Θ' u g y hθ
  simp [Ctx.refCross, normOr, h0, ho]

private theorem update_hist_value_eq {α β : Type*} [DecidableEq α]
    (f f' : α → β) (g : α) (ξ : β) (v : α) (hv : f v = f' v) :
    Function.update f g ξ v = Function.update f' g ξ v := by
  by_cases hvg : v = g
  · simp [Function.update, hvg]
  · simp [Function.update, hvg, hv]

private theorem intRatio_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (ξ : D.Tup)
    (h0 : Θ g = Θ' g) (hθ : ∀ u ∈ crossKeys g, Θ u = Θ' u)
    (o : Option D.M.ι) :
    D.intRatio Θ g ξ o = D.intRatio Θ' g ξ o := by
  cases o with
  | none => rfl
  | some i =>
    have h0u : Function.update Θ g ξ g = Function.update Θ' g ξ g := by simp
    have h1u : ∀ u ∈ crossKeys g,
        Function.update Θ g ξ u = Function.update Θ' g ξ u := by
      intro u hu
      exact update_hist_value_eq Θ Θ' g ξ u (hθ u hu)
    have htilt := tilt_weight_eq_of_hist_agree D (Function.update Θ g ξ)
      (Function.update Θ' g ξ) g h0u h1u i
    have href := refInt_weight_eq_of_hist_agree D Θ Θ' g hθ i
    simp [Ctx.intRatio, htilt, href]

private theorem crossRatio_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (ξ : D.Tup)
    (h1 : ∀ u ∈ crossKeys g, Θ u = Θ' u)
    (h2 : ∀ u ∈ crossKeys g, ∀ v ∈ crossKeys u, Θ v = Θ' v)
    (u : D.CrossSub g) (q : D.M.ι × Fin D.N) :
    D.crossRatio Θ g ξ u q = D.crossRatio Θ' g ξ u q := by
  have h0u : Function.update Θ g ξ g = Function.update Θ' g ξ g := by simp
  have hu : Function.update Θ g ξ u.1 = Function.update Θ' g ξ u.1 :=
    update_hist_value_eq Θ Θ' g ξ u.1 (h1 u.1 u.2)
  have hθu : ∀ v ∈ crossKeys u.1,
      Function.update Θ g ξ v = Function.update Θ' g ξ v := by
    intro v hv
    by_cases hvg : v = g
    · rw [hvg]
      simp [Function.update]
    · exact update_hist_value_eq Θ Θ' g ξ v (h2 u.1 u.2 v hv)
  have htilt := tilt_weight_eq_of_hist_agree D (Function.update Θ g ξ)
    (Function.update Θ' g ξ) u.1 hu hθu q.1
  have hanchor := anchorU_weight_eq_of_hist_agree D (Function.update Θ g ξ)
    (Function.update Θ' g ξ) u.1 hu hθu q.1 q.2
  have href := refCross_weight_eq_of_hist_agree D Θ Θ' g u.1
    (h1 u.1 u.2) (h2 u.1 u.2) q.1 q.2
  simp [Ctx.crossRatio, htilt, hanchor, href]

set_option maxHeartbeats 1000000 in
private theorem Mden_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (oi : D.Loc → Option D.M.ι)
    (ct : D.CrossSub g → D.M.ι)
    (h0 : Θ g = Θ' g)
    (h1 : ∀ u ∈ crossKeys g, Θ u = Θ' u)
    (h2 : ∀ u ∈ crossKeys g, ∀ v ∈ crossKeys u, Θ v = Θ' v)
    (x : D.CrossSub g → Fin D.N) :
    D.Mden Θ g (oi, fun u => (ct u, x u)) =
      D.Mden Θ' g (oi, fun u => (ct u, x u)) := by
  classical
  have hu0 (ξ : D.Tup) : Function.update Θ g ξ g = Function.update Θ' g ξ g := by simp
  have hu1 (ξ : D.Tup) : ∀ u ∈ crossKeys g,
      Function.update Θ g ξ u = Function.update Θ' g ξ u := by
    intro u hu
    exact update_hist_value_eq Θ Θ' g ξ u (h1 u hu)
  have hu2 (ξ : D.Tup) : ∀ u ∈ crossKeys g, ∀ v ∈ crossKeys u,
      Function.update Θ g ξ v = Function.update Θ' g ξ v := by
    intro u hu v hv
    by_cases hvg : v = g
    · rw [hvg]
      simp [Function.update]
    · exact update_hist_value_eq Θ Θ' g ξ v (h2 u hu v hv)
  have hFcand (ξ : D.Tup) :
      D.Fcand Θ g ξ (oi, fun u => (ct u, x u)) =
        D.Fcand Θ' g ξ (oi, fun u => (ct u, x u)) := by
    have hgate := candGate_eq_of_hist_agree D
      (Function.update Θ g ξ) (Function.update Θ' g ξ) g (hu0 ξ) (hu1 ξ) (hu2 ξ)
    have hint : ∀ o, D.intRatio Θ g ξ o = D.intRatio Θ' g ξ o :=
      fun o => intRatio_eq_of_hist_agree D Θ Θ' g ξ h0 h1 o
    have hcross : ∀ u : D.CrossSub g, ∀ q : D.M.ι × Fin D.N,
        D.crossRatio Θ g ξ u q = D.crossRatio Θ' g ξ u q :=
      fun u q => crossRatio_eq_of_hist_agree D Θ Θ' g ξ h1 h2 u q
    unfold Ctx.Fcand
    simp [hgate, hint, hcross]
  unfold Ctx.Mden
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [hFcand ξ]

private theorem qL_eq_of_parts (D : Ctx η₀ β p h) (Θ Θ' : D.Hist)
    (g : D.KeyT) (oi oi' : D.Loc → Option D.M.ι)
    (ct ct' : D.CrossSub g → D.M.ι)
    (hGate : D.CandGate Θ g = D.CandGate Θ' g)
    (hAnchor : ∀ u : D.CrossSub g, ∀ x : Fin D.N,
      (D.anchorU Θ u.1 (ct u)).w x = (D.anchorU Θ' u.1 (ct' u)).w x)
    (hM : ∀ x : D.CrossSub g → Fin D.N,
      D.Mden Θ g (oi, fun u => (ct u, x u)) =
        D.Mden Θ' g (oi', fun u => (ct' u, x u))) :
    D.qL Θ g oi ct = D.qL Θ' g oi' ct' := by
  classical
  unfold Ctx.qL
  apply Finset.sum_congr rfl
  intro x hx
  simp [hGate, hAnchor, hM x]

set_option maxHeartbeats 1000000 in
private theorem qL_eq_of_hist_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (g : D.KeyT) (oi : D.Loc → Option D.M.ι)
    (ct : D.CrossSub g → D.M.ι)
    (h0 : Θ g = Θ' g)
    (h1 : ∀ u ∈ crossKeys g, Θ u = Θ' u)
    (h2 : ∀ u ∈ crossKeys g, ∀ v ∈ crossKeys u, Θ v = Θ' v) :
    D.qL Θ g oi ct = D.qL Θ' g oi ct := by
  apply qL_eq_of_parts D Θ Θ' g oi oi ct ct
  · exact candGate_eq_of_hist_agree D Θ Θ' g h0 h1 h2
  · intro u x
    exact anchorU_weight_eq_of_hist_agree D Θ Θ' u.1 (h1 u.1 u.2) (h2 u.1 u.2)
      (ct u) x
  · intro x
    exact Mden_eq_of_hist_agree D Θ Θ' g oi ct h0 h1 h2 x

private theorem badList_eq_of_data_eq (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (t t' : D.Tags) (c : D.CellT) (L : D.LList c.1)
    (hInt : D.listInt t c.1 L = D.listInt t' c.1 L)
    (hCross : D.listCrossTag t c.1 L = D.listCrossTag t' c.1 L)
    (hQ : D.qL Θ c.1 (D.listInt t c.1 L) (D.listCrossTag t c.1 L) =
      D.qL Θ' c.1 (D.listInt t c.1 L) (D.listCrossTag t c.1 L)) :
    D.BadList Θ t c L ↔ D.BadList Θ' t' c L := by
  have hQ' := hQ
  rw [hInt, hCross] at hQ'
  unfold Ctx.BadList
  rw [hInt, hCross, hQ']

private theorem badList_eq_of_local_tag_agree (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (t t' : D.Tags) (P : D.Pos)
    (g : D.KeyT) (b b₀ : D.ResT) (c : D.CellT) (L : D.LList c.1)
    (hPad : PadNbr c (g, b))
    (hsite : _root_.hammingDist b b₀ ≤ 4 * HH η₀ D.n)
    (hΘ : ∀ u ∈ keyBall g 3, Θ u = Θ' u)
    (hTag : ∀ k ∈ keyBall g 2, ∀ ℓ : D.Loc,
      _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 → t k ℓ = t' k ℓ)
    (hCand : D.Cand P c L) :
    D.BadList Θ t c L ↔ D.BadList Θ' t' c L := by
  have hInt : D.listInt t c.1 L = D.listInt t' c.1 L := by
    funext ℓ
    by_cases hmem : ℓ ∈ L.1
    · have hbound : _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
        have hrad := cand_internal_radius D P hPad hCand hmem
        have hrad' : _root_.hammingDist ℓ.1 b ≤ rH D.n + 2 := by simpa using hrad
        have htri := _root_.hammingDist_triangle ℓ.1 b b₀
        omega
      have hkey := padNbr_cell_key_in_ball hPad
      have heq := hTag c.1 hkey ℓ hbound
      simp [Ctx.listInt, hmem, heq]
    · simp [Ctx.listInt, hmem]
  have hCross : D.listCrossTag t c.1 L = D.listCrossTag t' c.1 L := by
    funext u
    have hbound : _root_.hammingDist (L.2 u).1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by
      have hrad := cand_cross_radius D P hPad hCand u
      have hrad' : _root_.hammingDist (L.2 u).1 b ≤ rH D.n + 2 := by simpa using hrad
      have htri := _root_.hammingDist_triangle (L.2 u).1 b b₀
      omega
    have hkey := cross_of_padNbr_key_in_ball hPad u
    have heq := hTag u.1 hkey (L.2 u) hbound
    simp [Ctx.listCrossTag, heq]
  obtain ⟨h0, h1, h2⟩ := hist_agree_at_padNbr D Θ Θ' g b c hPad hΘ
  have hq := qL_eq_of_hist_agree D Θ Θ' c.1 (D.listInt t c.1 L)
    (D.listCrossTag t c.1 L) h0 h1 h2
  exact badList_eq_of_data_eq D Θ Θ' t t' c L hInt hCross hq

set_option maxHeartbeats 1000000 in
theorem elig_eq_of_local_inputs (D : Ctx η₀ β p h)
    (Θ Θ' : D.Hist) (P P' : D.Pos) (t t' : D.Tags)
    (g : D.KeyT) (b b₀ : D.ResT)
    (hsite : _root_.hammingDist b b₀ ≤ 4 * HH η₀ D.n)
    (hΘ : ∀ u ∈ keyBall g 3, Θ u = Θ' u)
    (hP : ∀ k ∈ keyBall g 2, ∀ ℓ : D.Loc,
      _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 → P k ℓ = P' k ℓ)
    (hTag : ∀ k ∈ keyBall g 2, ∀ ℓ : D.Loc,
      _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 → t k ℓ = t' k ℓ) :
    ∀ j, D.elig Θ P t g b j = D.elig Θ' P' t' g b j := by
  have hPsite : ∀ ℓ, _root_.hammingDist ℓ.1 b ≤ rH D.n → P g ℓ = P' g ℓ := by
    intro ℓ hdist
    have htri := _root_.hammingDist_triangle ℓ.1 b b₀
    have hbound : _root_.hammingDist ℓ.1 b₀ ≤ rH D.n + 4 * HH η₀ D.n + 2 := by omega
    have hg : g ∈ keyBall g 2 := by
      simp only [keyBall, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [keyDist]
    exact hP g hg ℓ hbound
  have hfamily : ∀ c : D.CellT, PadNbr c (g, b) →
      D.family Θ P t c = D.family Θ' P' t' c := by
    intro c hPad
    have hcand : ∀ L : D.LList c.1, D.Cand P c L ↔ D.Cand P' c L := by
      intro L
      exact cand_eq_of_local_pos_agree D P P' g b b₀ hsite hP c hPad L
    have hbad : ∀ L : D.LList c.1, D.Cand P c L → D.Cand P' c L →
        (D.BadList Θ t c L ↔ D.BadList Θ' t' c L) := by
      intro L hL hL'
      exact badList_eq_of_local_tag_agree D Θ Θ' t t' P g b b₀ c L
        hPad hsite hΘ hTag hL
    exact family_eq_of_candidate_bad_eq D Θ Θ' P P' t t' c hcand hbad
  have hF : ∀ ℓ,
      D.Forbidden Θ P t (g, b) ℓ ↔ D.Forbidden Θ' P' t' (g, b) ℓ := by
    intro ℓ
    exact forbidden_eq_of_family_eq D Θ Θ' P P' t t' (g, b) ℓ hfamily
  exact elig_site_eq_of_forbidden_eq D Θ Θ' P P' t t' g b hPsite hF

private theorem reach_endpoint_within (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    {v : CubeVertex p.d} {j : ℕ} (h : p.Reach Sites P A E vq R v j) :
    v ∈ Sites ∧ _root_.hammingDist v vq ≤ R := by
  induction h with
  | start v hv hd => exact ⟨hv, hd⟩
  | up v j hj hreach _ ih => exact ih
  | down v v' j hreach hv' hd _ ih => exact ⟨hv', hd⟩

private theorem reach_mono_elig (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E E' : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ R → E v = E' v)
    {v : CubeVertex p.d} {j : ℕ} (h : p.Reach Sites P A E vq R v j) :
    p.Reach Sites P A E' vq R v j := by
  induction h with
  | start v hv hd => exact .start v hv hd
  | up v j hj hreach hbad ih =>
      have hv := reach_endpoint_within p Sites P A E vq R hreach
      exact HDParams.Reach.up v j hj ih
        (by simpa [HDParams.BadN, HDParams.Bad, hE v hv.1 hv.2] using hbad)
  | down v v' j hreach hv' hd hstep ih => exact .down v v' j ih hv' hd hstep

private theorem reach_iff_elig (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E E' : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ R → E v = E' v)
    (v : CubeVertex p.d) (j : ℕ) :
    p.Reach Sites P A E vq R v j ↔ p.Reach Sites P A E' vq R v j := by
  constructor
  · exact reach_mono_elig p Sites P A E E' vq R hE
  · intro h
    apply reach_mono_elig p Sites P A E' E vq R
      (fun w hw hd => (hE w hw hd).symm) h

private theorem height_eq_elig (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E E' : p.EligMap) (R : ℕ) (vq : CubeVertex p.d)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ R → E v = E' v) :
    p.height Sites P A E R vq = p.height Sites P A E' R vq := by
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [reach_iff_elig p Sites P A E E' vq R hE]

theorem selection_eq_of_local_elig (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (E E' : p.EligMap) (τ : p.Ties) (vq : CubeVertex p.d)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ p.Rlong → E v = E' v)
    (hEvq : E vq = E' vq) :
    p.selection Sites P A E τ vq = p.selection Sites P A E' τ vq := by
  have hheight := height_eq_elig p Sites P A E E' p.Rlong vq
    hE
  simp [HDParams.selection, HDParams.selectionAt, HDParams.Bad, hheight, hEvq]

private theorem bad_eq_of_local_data (p : HDParams)
    (P P' A A' : p.Loc → Bool) (E E' : p.EligMap)
    (vq v : CubeVertex p.d) (R : ℕ) (j : Fin (p.H + 1))
    (hv : _root_.hammingDist v vq ≤ R) (hE : E v = E' v)
    (hGeom : ∀ j ℓ, ℓ ∈ E v j → _root_.hammingDist ℓ.1 v ≤ p.r)
    (hP : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → P ℓ = P' ℓ)
    (hA : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → A ℓ = A' ℓ) :
    p.Bad P A E v j = p.Bad P' A' E' v j := by
  apply propext
  have hEset : E v j = E' v j := by rw [hE]
  have hfirst : (∀ ℓ ∈ E v j, A ℓ = false) ↔ (∀ ℓ ∈ E' v j, A' ℓ = false) := by
    constructor
    · intro hh ℓ hℓ
      have hℓold : ℓ ∈ E v j := by simpa [hEset] using hℓ
      have hdist := hGeom j ℓ hℓold
      have htri := _root_.hammingDist_triangle ℓ.1 v vq
      have hbound : _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D := by omega
      rw [← hA ℓ hbound]
      exact hh ℓ hℓold
    · intro hh ℓ hℓ
      have hℓnew : ℓ ∈ E' v j := by simpa [hEset] using hℓ
      have hdist := hGeom j ℓ (by simpa [hEset] using hℓnew)
      have htri := _root_.hammingDist_triangle ℓ.1 v vq
      have hbound : _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D := by omega
      rw [hA ℓ hbound]
      exact hh ℓ hℓnew
  have hfilter :
      (Finset.univ.filter fun u : CubeVertex p.d =>
        P (u, j) = true ∧ A (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D) =
      (Finset.univ.filter fun u : CubeVertex p.d =>
        P' (u, j) = true ∧ A' (u, j) = true ∧ _root_.hammingDist u v ≤ p.r + p.D) := by
    apply Finset.ext
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨hp, ha, hd⟩
    · have htri := _root_.hammingDist_triangle u v vq
      have hbound : _root_.hammingDist u vq ≤ R + p.r + p.D := by omega
      have hloc : _root_.hammingDist (u, j).1 vq ≤ R + p.r + p.D := by simpa using hbound
      exact ⟨by rw [← hP (u, j) hloc]; exact hp,
        by rw [← hA (u, j) hloc]; exact ha, hd⟩
    · have htri := _root_.hammingDist_triangle u v vq
      have hbound : _root_.hammingDist u vq ≤ R + p.r + p.D := by omega
      have hloc : _root_.hammingDist (u, j).1 vq ≤ R + p.r + p.D := by simpa using hbound
      exact ⟨by rw [hP (u, j) hloc]; exact hp,
        by rw [hA (u, j) hloc]; exact ha, hd⟩
  have hcard := congrArg Finset.card hfilter
  simp only [HDParams.Bad, hfirst, hcard]

private theorem badN_eq_of_local_data (p : HDParams)
    (P P' A A' : p.Loc → Bool) (E E' : p.EligMap)
    (vq v : CubeVertex p.d) (R : ℕ)
    (hv : _root_.hammingDist v vq ≤ R) (hE : E v = E' v)
    (hGeom : ∀ j ℓ, ℓ ∈ E v j → _root_.hammingDist ℓ.1 v ≤ p.r)
    (hP : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → P ℓ = P' ℓ)
    (hA : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → A ℓ = A' ℓ)
    (k : ℕ) : p.BadN P A E v k = p.BadN P' A' E' v k := by
  apply propext
  unfold HDParams.BadN
  constructor <;> rintro ⟨hj, hbad⟩
  · exact ⟨hj, (bad_eq_of_local_data p P P' A A' E E' vq v R ⟨k, hj⟩
      hv hE hGeom hP hA).mp hbad⟩
  · exact ⟨hj, (bad_eq_of_local_data p P P' A A' E E' vq v R ⟨k, hj⟩
      hv hE hGeom hP hA).mpr hbad⟩

private theorem reach_mono_of_badN (p : HDParams) (Sites : p.Sites)
    (P P' A A' : p.Loc → Bool) (E E' : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    (hBad : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ R → ∀ j,
      p.BadN P A E v j → p.BadN P' A' E' v j)
    {v : CubeVertex p.d} {j : ℕ} (h : p.Reach Sites P A E vq R v j) :
    p.Reach Sites P' A' E' vq R v j := by
  induction h with
  | start v hv hd => exact .start v hv hd
  | up v j hj hreach hbad ih =>
      have hv := reach_endpoint_within p Sites P A E vq R hreach
      exact HDParams.Reach.up v j hj ih (hBad v hv.1 hv.2 j hbad)
  | down v v' j hreach hv' hd hstep ih => exact .down v v' j ih hv' hd hstep

private theorem reach_iff_local_data (p : HDParams) (Sites : p.Sites)
    (P P' A A' : p.Loc → Bool) (E E' : p.EligMap) (vq : CubeVertex p.d) (R : ℕ)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ R → E v = E' v)
    (hGeom : ∀ v ∈ Sites, ∀ j ℓ, ℓ ∈ E v j → _root_.hammingDist ℓ.1 v ≤ p.r)
    (hP : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → P ℓ = P' ℓ)
    (hA : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → A ℓ = A' ℓ)
    (v : CubeVertex p.d) (j : ℕ) :
    p.Reach Sites P A E vq R v j ↔ p.Reach Sites P' A' E' vq R v j := by
  have hBad (w : CubeVertex p.d) (hw : w ∈ Sites) (hd : _root_.hammingDist w vq ≤ R)
      (k : ℕ) : p.BadN P A E w k = p.BadN P' A' E' w k :=
    badN_eq_of_local_data p P P' A A' E E' vq w R hd (hE w hw hd)
      (hGeom w hw) hP hA k
  constructor
  · exact reach_mono_of_badN p Sites P P' A A' E E' vq R
      (fun w hw hd k hb => (hBad w hw hd k).mp hb)
  · intro hr
    exact reach_mono_of_badN p Sites P' P A' A E' E vq R
      (fun w hw hd k hb => (hBad w hw hd k).mpr hb) hr

private theorem height_eq_local_data (p : HDParams) (Sites : p.Sites)
    (P P' A A' : p.Loc → Bool) (E E' : p.EligMap) (R : ℕ) (vq : CubeVertex p.d)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ R → E v = E' v)
    (hGeom : ∀ v ∈ Sites, ∀ j ℓ, ℓ ∈ E v j → _root_.hammingDist ℓ.1 v ≤ p.r)
    (hP : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → P ℓ = P' ℓ)
    (hA : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ R + p.r + p.D → A ℓ = A' ℓ) :
    p.height Sites P A E R vq = p.height Sites P' A' E' R vq := by
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  rw [reach_iff_local_data p Sites P P' A A' E E' vq R hE hGeom hP hA]

theorem selection_eq_of_local_data (p : HDParams) (Sites : p.Sites)
    (P P' A A' : p.Loc → Bool) (E E' : p.EligMap) (τ τ' : p.Ties)
    (vq : CubeVertex p.d) (hvq : vq ∈ Sites)
    (hE : ∀ v ∈ Sites, _root_.hammingDist v vq ≤ p.Rlong → E v = E' v)
    (hGeom : ∀ v ∈ Sites, ∀ j ℓ, ℓ ∈ E v j → _root_.hammingDist ℓ.1 v ≤ p.r)
    (hP : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ p.Rlong + p.r + p.D → P ℓ = P' ℓ)
    (hA : ∀ ℓ, _root_.hammingDist ℓ.1 vq ≤ p.Rlong + p.r + p.D → A ℓ = A' ℓ)
    (hτ : ∀ j, τ (vq, j) = τ' (vq, j)) :
    p.selection Sites P A E τ vq = p.selection Sites P' A' E' τ' vq := by
  have hEvq : E vq = E' vq := hE vq hvq (by simp)
  have hheight := height_eq_local_data p Sites P P' A A' E E' p.Rlong vq
    hE hGeom hP hA
  have hbad (j : Fin (p.H + 1)) :
    p.Bad P A E vq j = p.Bad P' A' E' vq j :=
    bad_eq_of_local_data p P P' A A' E E' vq vq p.Rlong j (by simp)
      hEvq (hGeom vq hvq) hP hA
  have hactive (j : Fin (p.H + 1)) :
      (E vq j).filter (fun ℓ => A ℓ = true) =
        (E' vq j).filter (fun ℓ => A' ℓ = true) := by
    have hEj : E vq j = E' vq j := congrArg (fun F => F j) hEvq
    apply Finset.ext
    intro ℓ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmem, ha⟩
      have hmem' : ℓ ∈ E' vq j := by simpa [hEj] using hmem
      have hdist := hGeom vq hvq j ℓ hmem
      have hbound : _root_.hammingDist ℓ.1 vq ≤ p.Rlong + p.r + p.D := by omega
      exact ⟨hmem', by rw [← hA ℓ hbound]; exact ha⟩
    · rintro ⟨hmem, ha⟩
      have hmem' : ℓ ∈ E vq j := by simpa [hEj] using hmem
      have hdist := hGeom vq hvq j ℓ hmem'
      have hbound : _root_.hammingDist ℓ.1 vq ≤ p.Rlong + p.r + p.D := by omega
      exact ⟨hmem', by rw [hA ℓ hbound]; exact ha⟩
  simp [HDParams.selection, HDParams.selectionAt, HDParams.priority,
    hheight, hbad, hactive, hτ]

set_option maxHeartbeats 1000000 in
theorem preLaw_expect_noTie (D : Ctx η₀ β p h)
    (F : D.Pos → D.Hist → D.Tags → D.Acts → ℝ) :
    D.preLaw.expect (fun q => F q.1.2 q.1.1 q.2.1.1 q.2.1.2) =
    let auxLaw : FinProb (D.Hist × D.Tags) :=
      FinProb.bind D.hiddenLaw (fun Θ => D.tagLawAll Θ);
      ((D.posLaw.prod auxLaw).prod D.actLaw).expect
        (fun z => F z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  classical
  simp only [Ctx.preLaw, Ctx.rawTAT, FinProb.expect, FinProb.bind, FinProb.prod]
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ Θ : D.Hist, ∑ P : D.Pos, ∑ T : D.Tags, ∑ A : D.Acts,
        D.hiddenLaw.w Θ * D.posLaw.w P * (D.tagLawAll Θ).w T * D.actLaw.w A * F P Θ T A := by
      apply Fintype.sum_congr
      intro Θ
      apply Fintype.sum_congr
      intro P
      apply Fintype.sum_congr
      intro T
      apply Fintype.sum_congr
      intro A
      calc
        _ = ∑ W : D.TieAll,
            (D.hiddenLaw.w Θ * D.posLaw.w P *
              ((D.tagLawAll Θ).w T * D.actLaw.w A * D.tieLaw.w W) * F P Θ T A) := by
          apply Fintype.sum_congr
          intro W
          rfl
        _ = (D.hiddenLaw.w Θ * D.posLaw.w P * (D.tagLawAll Θ).w T *
              D.actLaw.w A * F P Θ T A) * ∑ W : D.TieAll, D.tieLaw.w W := by
          calc
            _ = ∑ W : D.TieAll,
                (D.hiddenLaw.w Θ * D.posLaw.w P * (D.tagLawAll Θ).w T *
                  D.actLaw.w A * F P Θ T A) * D.tieLaw.w W := by
              apply Fintype.sum_congr
              intro W
              ring
            _ = _ := by rw [Finset.mul_sum]
        _ = D.hiddenLaw.w Θ * D.posLaw.w P * (D.tagLawAll Θ).w T *
              D.actLaw.w A * F P Θ T A := by simp [D.tieLaw.sum_eq_one]
    _ = ∑ P : D.Pos, ∑ Θ : D.Hist, ∑ T : D.Tags, ∑ A : D.Acts,
        D.posLaw.w P * (D.hiddenLaw.w Θ * (D.tagLawAll Θ).w T) *
          D.actLaw.w A * F P Θ T A := by
      rw [Finset.sum_comm]
      apply Fintype.sum_congr
      intro P
      apply Fintype.sum_congr
      intro Θ
      apply Fintype.sum_congr
      intro T
      apply Fintype.sum_congr
      intro A
      ring

private theorem nonempty_of_finProb {α : Type*} [Fintype α] (P : FinProb α) : Nonempty α := by
  classical
  by_contra h
  haveI : IsEmpty α := ⟨fun a => h ⟨a⟩⟩
  have hsum : (∑ a, P.w a) = 0 := by simp
  rw [P.sum_eq_one] at hsum
  norm_num at hsum

theorem pi_expect_coordinate {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (P : FinProb α) (i₀ : ι) (f : α → ℝ) :
    (FinProb.pi (fun _ : ι => P)).expect (fun ω => f (ω i₀)) = P.expect f := by
  classical
  let s : Finset ι := {i₀}
  let F : (ι → α) → ℝ := fun ω => f (ω i₀)
  let ω₀ : ι → α := fun _ => Classical.choice (nonempty_of_finProb P)
  have hdep : FinProb.DependsOn F s := by
    intro ω ω' hagree
    dsimp [F]
    rw [hagree i₀ (by simp [s])]
  have hsplit := FinProb.pi_expect_depends (fun _ : ι => P) s F ω₀ hdep
  let inst : Unique {i // i ∈ s} := {
    default := ⟨i₀, by simp [s]⟩
    uniq := by
      intro j
      apply Subtype.ext
      exact Finset.mem_singleton.mp (by simpa [s] using j.2)
  }
  letI : Unique {i // i ∈ s} := inst
  let e : (∀ _ : {i // i ∈ s}, α) ≃ α := Equiv.piUnique _
  have hsingle :
      (FinProb.pi (fun _ : {i // i ∈ s} => P)).expect (fun a => f (a default)) = P.expect f := by
    unfold FinProb.expect
    rw [← Equiv.sum_comp e.symm
      (fun a => (FinProb.pi (fun _ : {i // i ∈ s} => P)).w a * f (a default))]
    simp [FinProb.pi, e, inst]
  have hproj : ∀ a : (∀ _ : {i // i ∈ s}, α),
      F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ : ι => α)).symm
        (a, fun i => ω₀ i.1)) = f (a default) := by
    intro a
    simp [F, s]
    have hx : (⟨i₀, by simp [s]⟩ : {i // i ∈ s}) = default := Subsingleton.elim _ _
    rw [hx]
  calc
    (FinProb.pi (fun _ : ι => P)).expect (fun ω => f (ω i₀)) =
        (FinProb.pi (fun _ : {i // i ∈ s} => P)).expect
          (fun a => F ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ s) (fun _ : ι => α)).symm
            (a, fun i => ω₀ i.1))) := by
              simpa [F] using hsplit
    _ = (FinProb.pi (fun _ : {i // i ∈ s} => P)).expect
          (fun a => f (a default)) := by
            congr 1
            funext a
            exact hproj a
    _ = P.expect f := hsingle

private theorem expect_prod_left {A B : Type*} [Fintype A] [Fintype B]
    (P : FinProb A) (Q : FinProb B) (f : A → ℝ) :
    (P.prod Q).expect (fun z => f z.1) = P.expect f := by
  classical
  unfold FinProb.expect FinProb.prod
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, P.w a * Q.w b * f a) =
        ∑ a, (P.w a * f a) * ∑ b, Q.w b := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ b, P.w a * Q.w b * f a) =
            ∑ b, (P.w a * f a) * Q.w b := by
              apply Finset.sum_congr rfl
              intro b hb
              ring
        _ = (P.w a * f a) * ∑ b, Q.w b := by rw [Finset.mul_sum]
    _ = ∑ a, P.w a * f a := by simp [Q.sum_eq_one]

theorem preLaw_expect_pos (D : Ctx η₀ β p h) (f : D.Pos → ℝ) :
    D.preLaw.expect (fun q => f q.1.2) = D.posLaw.expect f := by
  classical
  let auxLaw : FinProb (D.Hist × D.Tags) :=
    FinProb.bind D.hiddenLaw (fun Θ => D.tagLawAll Θ)
  let F : D.Pos → D.Hist → D.Tags → D.Acts → ℝ := fun P _ _ _ => f P
  have hNoTie := preLaw_expect_noTie D F
  calc
    D.preLaw.expect (fun q => f q.1.2) =
        ((D.posLaw.prod auxLaw).prod D.actLaw).expect
        (fun z => f z.1.1) := by
            simpa [auxLaw, F] using hNoTie
    _ = (D.posLaw.prod auxLaw).expect (fun z => f z.1) :=
      expect_prod_left (D.posLaw.prod auxLaw) D.actLaw (fun z => f z.1)
    _ = D.posLaw.expect f := expect_prod_left D.posLaw auxLaw f

noncomputable def prIndicator {Ω : Type*} (A : Ω → Prop) : Ω → ℝ := by
  classical
  exact fun ω => if A ω then 1 else 0

theorem pr_eq_expect_indicator {Ω : Type*} [Fintype Ω]
    (P : FinProb Ω) (A : Ω → Prop) :
    P.pr A = P.expect (prIndicator A) := by
  classical
  unfold FinProb.pr FinProb.expect prIndicator
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases h : A ω <;> simp [h]

theorem choose20_lower {d : ℕ} (hd : 40 ≤ d) :
    (d : ℝ) ^ 20 / ((3 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ)) ≤
      (Nat.choose d 20 : ℝ) := by
  have hdescNat : (d / 2) ^ 20 ≤ d.descFactorial 20 := by
    rw [Nat.descFactorial_eq_prod_range]
    calc
      (d / 2) ^ 20 = ∏ i ∈ Finset.range 20, d / 2 := by simp
      _ ≤ ∏ i ∈ Finset.range 20, (d - i) := by
        apply Finset.prod_le_prod
        intro i hi
        have hi' : i < 20 := Finset.mem_range.mp hi
        omega
  have hdescReal : ((d / 2 : ℕ) : ℝ) ^ 20 ≤ (d.descFactorial 20 : ℝ) := by
    exact_mod_cast hdescNat
  have hdivNat : d ≤ 3 * (d / 2) := by omega
  have hdivReal : (d : ℝ) / 3 ≤ ((d / 2 : ℕ) : ℝ) := by
    have hcast : (d : ℝ) ≤ 3 * ((d / 2 : ℕ) : ℝ) := by exact_mod_cast hdivNat
    linarith
  have hpow : ((d : ℝ) / 3) ^ 20 ≤ ((d / 2 : ℕ) : ℝ) ^ 20 :=
    pow_le_pow_left₀ (by positivity) hdivReal 20
  have hiden : d.descFactorial 20 = Nat.factorial 20 * Nat.choose d 20 :=
    Nat.descFactorial_eq_factorial_mul_choose d 20
  have hidenR : (d.descFactorial 20 : ℝ) =
      (Nat.factorial 20 : ℝ) * (Nat.choose d 20 : ℝ) := by exact_mod_cast hiden
  have hfact : (0 : ℝ) < (Nat.factorial 20 : ℝ) := by positivity
  calc
    (d : ℝ) ^ 20 / ((3 : ℝ) ^ 20 * (Nat.factorial 20 : ℝ)) =
        ((d : ℝ) / 3) ^ 20 / (Nat.factorial 20 : ℝ) := by rw [div_pow]; ring
    _ ≤ ((d / 2 : ℕ) : ℝ) ^ 20 / (Nat.factorial 20 : ℝ) :=
      div_le_div_of_nonneg_right hpow hfact.le
    _ ≤ (d.descFactorial 20 : ℝ) / (Nat.factorial 20 : ℝ) :=
      div_le_div_of_nonneg_right hdescReal hfact.le
    _ = (Nat.choose d 20 : ℝ) := by rw [hidenR]; field_simp

private theorem scaleIndex_exists_grid (M R target : ℕ) (hM : 2 ≤ M) (hR : 1 ≤ R) :
    ∃ i : ℕ, target ≤ M ^ i * R := by
  have hM0 : M ≠ 0 := by omega
  induction target with
  | zero => exact ⟨0, by simp⟩
  | succ target ih =>
      obtain ⟨i, hi⟩ := ih
      let x := M ^ i * R
      have hx0 : x ≠ 0 := by
        dsimp [x]
        exact Nat.mul_ne_zero (pow_ne_zero _ hM0) (by omega)
      have hx : 1 ≤ x := by omega
      have hstep : x + 1 ≤ 2 * x := by omega
      have hmult : 2 * x ≤ M * x := Nat.mul_le_mul_right x hM
      refine ⟨i + 1, ?_⟩
      calc
        target + 1 ≤ x + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * x := hstep
        _ ≤ M * x := hmult
        _ = M ^ (i + 1) * R := by dsimp [x]; rw [pow_succ]; ring

private theorem findScale_le_mul_target (M R target : ℕ)
    (hP : ∃ i : ℕ, target ≤ M ^ i * R) (hM : 2 ≤ M) (hR : 1 ≤ R)
    (hRT : R ≤ target) : M ^ Nat.find hP * R ≤ M * target := by
  have hspec : target ≤ M ^ Nat.find hP * R := Nat.find_spec hP
  by_cases hi : Nat.find hP = 0
  · have hEq : R = target := by
      have hle : target ≤ R := by simpa [hi] using hspec
      exact Nat.le_antisymm hRT hle
    rw [hi, hEq, pow_zero, one_mul]
    calc
      target = 1 * target := by simp
      _ ≤ M * target := Nat.mul_le_mul_right target (by omega)
  · have hpos : 1 ≤ Nat.find hP := by omega
    have hpowEq : M ^ Nat.find hP = M ^ (Nat.find hP - 1 + 1) := by
      rw [Nat.sub_add_cancel hpos]
    have hprev : ¬ target ≤ M ^ (Nat.find hP - 1) * R :=
      Nat.find_min hP (by omega)
    have hlt : M ^ (Nat.find hP - 1) * R < target := Nat.lt_of_not_ge hprev
    have hpow : M ^ Nat.find hP * R = M * (M ^ (Nat.find hP - 1) * R) := by
      calc
        M ^ Nat.find hP * R = M ^ ((Nat.find hP - 1) + 1) * R := by rw [hpowEq]
        _ = (M ^ (Nat.find hP - 1) * M) * R := by rw [pow_succ]
        _ = M * (M ^ (Nat.find hP - 1) * R) := by ring
    rw [hpow]
    exact Nat.mul_le_mul_left M hlt.le

private theorem topScale_eq_grid_formula (n : ℕ) (σ ζ : ℝ) :
    topScale n σ ζ =
      (max 2 ⌈(n : ℝ) ^ σ⌉₊) ^ Nat.find
        (scaleIndex_exists_grid (max 2 ⌈(n : ℝ) ^ σ⌉₊)
          (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) ⌈(n : ℝ) ^ (1 - ζ)⌉₊
          (by omega) (by omega)) * max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ := by
  unfold topScale
  congr 1

theorem topScale_le_mul_target (n : ℕ) (σ ζ : ℝ)
    (hR0 : max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ ⌈(n : ℝ) ^ (1 - ζ)⌉₊) :
    topScale n σ ζ ≤ (max 2 ⌈(n : ℝ) ^ σ⌉₊) * ⌈(n : ℝ) ^ (1 - ζ)⌉₊ := by
  let R₀ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let target := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hM : 2 ≤ M := by simp [M]
  have hR : 1 ≤ R₀ := by simp [R₀]
  rw [topScale_eq_grid_formula]
  exact findScale_le_mul_target M R₀ target
    (scaleIndex_exists_grid M R₀ target hM hR) hM hR (by simpa [R₀, target] using hR0)

theorem gridScaleBounds (η₀ : ℝ) (hη₀ : 0 < η₀) :
    ∃ n₀, ∀ n ≥ n₀, sC η₀ n ≤ n ∧ TC η₀ n ≤ n ∧ HH η₀ n ≤ n := by
  obtain ⟨hσpos, hσζ, hζ1, _, _⟩ := (hd_admissible η₀ hη₀).hsz
  have hζpos : 0 < zetaH η₀ := lt_trans hσpos hσζ
  have hσ1 : sigmaH η₀ < 1 := lt_trans hσζ hζ1
  have hη8pos : 0 < eta8 η₀ := by
    change 0 < min (η₀ / 2) (4 / 100 : ℝ)
    exact lt_min (by linarith) (by norm_num)
  have hτpos : 0 < tau8 η₀ := by
    rw [tau8_eq]
    exact div_pos hη8pos (by norm_num)
  have hτ1 : tau8 η₀ < 1 := by
    rw [tau8_eq]
    have hη8 : eta8 η₀ ≤ 4 / 100 := min_le_right _ _
    linarith
  let a : ℝ := 1 - zetaH η₀
  have ha : 0 < a := by dsimp [a]; linarith
  let δ : ℝ := zetaH η₀ - sigmaH η₀
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let cLog : ℝ := (4 / a) ^ 2
  have hLogT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (a / 2))
      Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : (0 : ℝ) < a / 2)).comp
      tendsto_natCast_atTop_atTop
  have hLogEventually : ∀ᶠ n : ℕ in Filter.atTop, cLog ≤ (n : ℝ) ^ (a / 2) :=
    hLogT.eventually (Filter.eventually_ge_atTop cLog)
  obtain ⟨nLog, hLog⟩ := Filter.eventually_atTop.1 hLogEventually
  have hGapT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ δ) Filter.atTop Filter.atTop :=
    (_root_.tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  have hGapEventually : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ (n : ℝ) ^ δ :=
    hGapT.eventually (Filter.eventually_ge_atTop 4)
  obtain ⟨nGap, hGap⟩ := Filter.eventually_atTop.1 hGapEventually
  refine ⟨max 2 (max nLog nGap), ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by omega
  have hnLog : nLog ≤ n := by omega
  have hnGap : nGap ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hpowLog : cLog ≤ (n : ℝ) ^ (a / 2) := hLog n hnLog
  have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogBound : Real.log (n : ℝ) ≤ ((n : ℝ) ^ (a / 4)) / (a / 4) :=
    Real.log_natCast_le_rpow_div n (by linarith)
  have hlogSq : (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ a := by
    have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (((n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 :=
      (sq_le_sq₀ hlogNonneg (by positivity)).2 hlogBound
    calc
      (Real.log (n : ℝ)) ^ 2 ≤ (((n : ℝ) ^ (a / 4)) / (a / 4)) ^ 2 := hsq
      _ = cLog * (n : ℝ) ^ (a / 2) := by
        dsimp [cLog]
        rw [div_pow]
        have hpow : ((n : ℝ) ^ (a / 4)) ^ 2 = (n : ℝ) ^ (a / 2) := by
          calc
            ((n : ℝ) ^ (a / 4)) ^ 2 = ((n : ℝ) ^ (a / 4)) ^ (2 : ℝ) :=
              (Real.rpow_natCast ((n : ℝ) ^ (a / 4)) 2).symm
            _ = (n : ℝ) ^ ((a / 4) * 2) :=
              (Real.rpow_mul (x := (n : ℝ)) (by positivity) (a / 4) 2).symm
            _ = (n : ℝ) ^ (a / 2) := by congr 1 <;> ring
        rw [hpow]
        have heps : (a / 4) ≠ 0 := ne_of_gt (by linarith)
        field_simp [heps]
      _ ≤ (n : ℝ) ^ (a / 2) * (n : ℝ) ^ (a / 2) :=
        mul_le_mul_of_nonneg_right hpowLog (Real.rpow_nonneg (by positivity) _)
      _ = (n : ℝ) ^ a := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ))]
        congr 1 <;> ring
  have hR0 : max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ ⌈(n : ℝ) ^ a⌉₊ := by
    have hceilLog : ⌈Real.log (n : ℝ) ^ 2⌉₊ ≤ ⌈(n : ℝ) ^ a⌉₊ :=
      Nat.ceil_le.mpr (hlogSq.trans (Nat.le_ceil ((n : ℝ) ^ a)))
    have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ a := Real.one_le_rpow hnR (by linarith)
    have hceilOne : 1 ≤ ⌈(n : ℝ) ^ a⌉₊ := by
      exact_mod_cast (le_trans hpowOne (Nat.le_ceil ((n : ℝ) ^ a)))
    exact max_le hceilOne hceilLog
  have hTop := topScale_le_mul_target n (sigmaH η₀) (zetaH η₀) hR0
  have hpowσ : (n : ℝ) ^ sigmaH η₀ ≤ (n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR hσ1.le
  have hpowA : (n : ℝ) ^ a ≤ (n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by dsimp [a]; linarith [hζpos])
  have hceilσ : ⌈(n : ℝ) ^ sigmaH η₀⌉₊ ≤ n := Nat.ceil_le.mpr (by simpa using hpowσ)
  have hceilA : ⌈(n : ℝ) ^ a⌉₊ ≤ n := Nat.ceil_le.mpr (by simpa using hpowA)
  have hs : sC η₀ n ≤ n := by
    unfold sC
    exact Nat.ceil_le.mpr (by
      simpa using Real.rpow_le_rpow_of_exponent_le hnR hτ1.le)
  have hT : TC η₀ n ≤ n := by
    unfold TC
    have hTexp : tau8 η₀ / 8 ≤ 1 := by linarith [hτ1]
    exact Nat.ceil_le.mpr (by
      simpa using Real.rpow_le_rpow_of_exponent_le hnR hTexp)
  have hMfactor : (max 2 ⌈(n : ℝ) ^ sigmaH η₀⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ sigmaH η₀ := by
    change max (2 : ℝ) (⌈(n : ℝ) ^ sigmaH η₀⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ sigmaH η₀
    have hσbase : (1 : ℝ) ≤ (n : ℝ) ^ sigmaH η₀ := Real.one_le_rpow hnR hσpos.le
    apply max_le
    · nlinarith [hσbase]
    · have hceil : (⌈(n : ℝ) ^ sigmaH η₀⌉₊ : ℝ) < (n : ℝ) ^ sigmaH η₀ + 1 :=
        Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
      linarith [hσbase]
  have hTargetFactor : (⌈(n : ℝ) ^ a⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ a := by
    have hceil : (⌈(n : ℝ) ^ a⌉₊ : ℝ) < (n : ℝ) ^ a + 1 :=
      Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
    have habase : (1 : ℝ) ≤ (n : ℝ) ^ a := Real.one_le_rpow hnR ha.le
    linarith [habase]
  have hHHreal : (HH η₀ n : ℝ) ≤ 4 * (n : ℝ) ^ (sigmaH η₀ + a) := by
    have hTopCast : (HH η₀ n : ℝ) ≤
        (max 2 ⌈(n : ℝ) ^ sigmaH η₀⌉₊ : ℝ) * (⌈(n : ℝ) ^ a⌉₊ : ℝ) := by
      have hTopNat : HH η₀ n ≤
          max 2 ⌈(n : ℝ) ^ sigmaH η₀⌉₊ * ⌈(n : ℝ) ^ a⌉₊ := by
        simpa [HH, a] using hTop
      exact_mod_cast hTopNat
    have hmul : ((max 2 ⌈(n : ℝ) ^ sigmaH η₀⌉₊ : ℝ) *
        (⌈(n : ℝ) ^ a⌉₊ : ℝ)) ≤ 4 * (n : ℝ) ^ (sigmaH η₀ + a) := by
      calc
        _ ≤ (2 * (n : ℝ) ^ sigmaH η₀) * (2 * (n : ℝ) ^ a) :=
          mul_le_mul hMfactor hTargetFactor (by positivity) (by positivity)
        _ = 4 * ((n : ℝ) ^ sigmaH η₀ * (n : ℝ) ^ a) := by ring
        _ = 4 * (n : ℝ) ^ (sigmaH η₀ + a) := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ))]
    exact hTopCast.trans hmul
  have hGapPow : (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ δ = (n : ℝ) := by
    calc
      (n : ℝ) ^ (1 - δ) * (n : ℝ) ^ δ = (n : ℝ) ^ ((1 - δ) + δ) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < (n : ℝ))]
      _ = (n : ℝ) ^ (1 : ℝ) := by congr 1 <;> ring
      _ = (n : ℝ) := Real.rpow_one _
  have hHNat : HH η₀ n ≤ n := by
    have hExpEq : sigmaH η₀ + a = 1 - δ := by dsimp [a, δ]; ring
    have hHreal : (HH η₀ n : ℝ) ≤ (n : ℝ) := by
      calc
        (HH η₀ n : ℝ) ≤ 4 * (n : ℝ) ^ (sigmaH η₀ + a) := hHHreal
        _ = 4 * (n : ℝ) ^ (1 - δ) := by rw [hExpEq]
        _ ≤ (n : ℝ) ^ δ * (n : ℝ) ^ (1 - δ) :=
          mul_le_mul_of_nonneg_right (hGap n hnGap) (Real.rpow_nonneg (by positivity) _)
        _ = (n : ℝ) := by rw [mul_comm, hGapPow]
    exact_mod_cast hHreal
  exact ⟨hs, hT, hHNat⟩

/-! ### Flattening the nested tag product

The experiment samples a product over keys, each of which is itself a product over locations.  For disjoint-list
independence it is useful to expose the same law as a product over `(key, location)` coordinates. -/

private def tagCoordinatesEquiv (D : Ctx η₀ β p h) :
    D.Tags ≃ (D.KeyT × D.Loc → D.M.ι) where
  toFun t i := t i.1 i.2
  invFun t g ℓ := t (g, ℓ)
  left_inv t := by funext g ℓ; rfl
  right_inv t := by funext i; cases i; rfl

private def tagCoordinatesPullback (D : Ctx η₀ β p h) (t : D.KeyT × D.Loc → D.M.ι) : D.Tags :=
  (tagCoordinatesEquiv D).symm t

@[simp] private theorem tagCoordinatesPullback_reconstruct (D : Ctx η₀ β p h) (t : D.Tags) :
    tagCoordinatesPullback D (fun i => t i.1 i.2) = t := by
  funext g ℓ
  rfl

theorem tagLawAll_map_coordinates (D : Ctx η₀ β p h) (Θ : D.Hist) :
    FinProb.map (D.tagLawAll Θ) (tagCoordinatesEquiv D) =
      FinProb.pi (fun i : D.KeyT × D.Loc => D.tilt Θ i.1) := by
  classical
  apply finProb_ext
  funext t
  change (∑ x : D.Tags,
      if tagCoordinatesEquiv D x = t then (D.tagLawAll Θ).w x else 0) =
    ∏ i : D.KeyT × D.Loc, (D.tilt Θ i.1).w (t i)
  calc
    _ = ∑ y : D.KeyT × D.Loc → D.M.ι,
        if y = t then (D.tagLawAll Θ).w ((tagCoordinatesEquiv D).symm y) else 0 := by
      apply Fintype.sum_equiv (tagCoordinatesEquiv D)
      intro x
      simp [tagCoordinatesEquiv]
    _ = (D.tagLawAll Θ).w ((tagCoordinatesEquiv D).symm t) := by simp
    _ = ∏ i : D.KeyT × D.Loc, (D.tilt Θ i.1).w (t i) := by
      change (∏ g : D.KeyT, ∏ ℓ : D.Loc, (D.tilt Θ g).w (t (g, ℓ))) = _
      exact (Fintype.prod_prod_type' (fun g ℓ => (D.tilt Θ g).w (t (g, ℓ)))).symm

theorem tagLawAll_expect_coordinates (D : Ctx η₀ β p h) (Θ : D.Hist)
    (f : (D.KeyT × D.Loc → D.M.ι) → ℝ) :
    (D.tagLawAll Θ).expect (fun t => f (fun i => t i.1 i.2)) =
      (FinProb.pi (fun i : D.KeyT × D.Loc => D.tilt Θ i.1)).expect f := by
  classical
  calc
    _ = (FinProb.map (D.tagLawAll Θ) (tagCoordinatesEquiv D)).expect f :=
      (FinProb.map_expect _ _ _).symm
    _ = (FinProb.pi (fun i : D.KeyT × D.Loc => D.tilt Θ i.1)).expect f := by
      rw [tagLawAll_map_coordinates]

private theorem badList_depends_on_listIds (D : Ctx η₀ β p h) (Θ : D.Hist)
    (c : D.CellT) (L : D.LList c.1) :
    FinProb.DependsOn (fun t : D.KeyT × D.Loc → D.M.ι =>
      D.BadList Θ (tagCoordinatesPullback D t) c L) (D.listIds c.1 L) := by
  classical
  intro t t' htags
  have hInternal :
      D.listInt (tagCoordinatesPullback D t) c.1 L =
        D.listInt (tagCoordinatesPullback D t') c.1 L := by
    funext ℓ
    by_cases hℓ : ℓ ∈ L.1
    · have hmem : (c.1, ℓ) ∈ D.listIds c.1 L := by
        unfold Ctx.listIds
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩)
      simp only [Ctx.listInt, if_pos hℓ, Option.some.injEq]
      exact htags (c.1, ℓ) hmem
    · simp [Ctx.listInt, hℓ]
  have hCross :
      D.listCrossTag (tagCoordinatesPullback D t) c.1 L =
        D.listCrossTag (tagCoordinatesPullback D t') c.1 L := by
    funext u
    have hmem : (u.1, L.2 u) ∈ D.listIds c.1 L := by
      unfold Ctx.listIds
      apply Finset.mem_union_right
      simp
    exact htags (u.1, L.2 u) hmem
  have hq :
      D.qL Θ c.1 (D.listInt (tagCoordinatesPullback D t) c.1 L)
          (D.listCrossTag (tagCoordinatesPullback D t) c.1 L) =
        D.qL Θ c.1 (D.listInt (tagCoordinatesPullback D t') c.1 L)
          (D.listCrossTag (tagCoordinatesPullback D t') c.1 L) := by
    rw [hInternal, hCross]
  change (Real.sqrt (Real.sqrt D.eps0) <
      D.qL Θ c.1 (D.listInt (tagCoordinatesPullback D t) c.1 L)
        (D.listCrossTag (tagCoordinatesPullback D t) c.1 L)) =
    (Real.sqrt (Real.sqrt D.eps0) <
      D.qL Θ c.1 (D.listInt (tagCoordinatesPullback D t') c.1 L)
        (D.listCrossTag (tagCoordinatesPullback D t') c.1 L))
  rw [hq]

private theorem badList_pair_probability_mul (D : Ctx η₀ β p h) (Θ : D.Hist)
    (c : D.CellT) (L : D.LList c.1) (c' : D.CellT) (L' : D.LList c'.1)
    (hdis : Disjoint (D.listIds c.1 L) (D.listIds c'.1 L')) :
    (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L ∧ D.BadList Θ t c' L') =
      (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L) *
        (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c' L') := by
  classical
  let Q : FinProb (D.KeyT × D.Loc → D.M.ι) :=
    FinProb.pi (fun i : D.KeyT × D.Loc => D.tilt Θ i.1)
  let A : (D.KeyT × D.Loc → D.M.ι) → Prop := fun t =>
    D.BadList Θ (tagCoordinatesPullback D t) c L
  let B : (D.KeyT × D.Loc → D.M.ι) → Prop := fun t =>
    D.BadList Θ (tagCoordinatesPullback D t) c' L'
  let f : (D.KeyT × D.Loc → D.M.ι) → ℝ := fun t => prIndicator (A) t
  let g : (D.KeyT × D.Loc → D.M.ι) → ℝ := fun t => prIndicator (B) t
  have hf : FinProb.DependsOn f (D.listIds c.1 L) := by
    intro t t' ht
    have hbad := badList_depends_on_listIds D Θ c L t t' ht
    simp [f, prIndicator, A, hbad]
  have hg : FinProb.DependsOn g (D.listIds c'.1 L') := by
    intro t t' ht
    have hbad := badList_depends_on_listIds D Θ c' L' t t' ht
    simp [g, prIndicator, B, hbad]
  have hmul := FinProb.pi_expect_mul_of_disjoint
    (fun i : D.KeyT × D.Loc => D.tilt Θ i.1) f g
      (D.listIds c.1 L) (D.listIds c'.1 L') hf hg hdis
  have hprA : (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L) = Q.expect f := by
    rw [pr_eq_expect_indicator]
    have hfun : prIndicator (fun t => D.BadList Θ t c L) =
        fun t => f (fun i => t i.1 i.2) := by
      funext t
      change (if D.BadList Θ t c L then 1 else 0) =
        (if D.BadList Θ t c L then 1 else 0)
      rfl
    rw [hfun]
    simpa [Q] using tagLawAll_expect_coordinates D Θ f
  have hprB : (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c' L') = Q.expect g := by
    rw [pr_eq_expect_indicator]
    have hfun : prIndicator (fun t => D.BadList Θ t c' L') =
        fun t => g (fun i => t i.1 i.2) := by
      funext t
      change (if D.BadList Θ t c' L' then 1 else 0) =
        (if D.BadList Θ t c' L' then 1 else 0)
      rfl
    rw [hfun]
    simpa [Q] using tagLawAll_expect_coordinates D Θ g
  have hprAB :
      (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L ∧ D.BadList Θ t c' L') =
        Q.expect (fun t => f t * g t) := by
    rw [pr_eq_expect_indicator]
    have hfun : prIndicator (fun t => D.BadList Θ t c L ∧ D.BadList Θ t c' L') =
        fun t => f (fun i => t i.1 i.2) * g (fun i => t i.1 i.2) := by
      funext t
      dsimp [prIndicator, f, g, A, B]
      simp only [tagCoordinatesPullback_reconstruct]
      by_cases hA : D.BadList Θ t c L <;> by_cases hB : D.BadList Θ t c' L' <;>
        simp [hA, hB]
    rw [hfun]
    simpa [Q] using tagLawAll_expect_coordinates D Θ (fun t => f t * g t)
  calc
    (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L ∧ D.BadList Θ t c' L') =
        Q.expect (fun t => f t * g t) := hprAB
    _ = Q.expect f * Q.expect g := hmul
    _ = (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c L) *
        (D.tagLawAll Θ).pr (fun t => D.BadList Θ t c' L') := by rw [hprA, hprB]

end HypercubeRamsey.Lane_q_s08_sel
