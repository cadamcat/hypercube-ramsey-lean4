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
