import HypercubeRamsey.S04.CoreLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Helpers for the Section 4 profile proofs in lane q-s04-prof.
-/

namespace HypercubeRamsey.Lane_q_s04_prof

open Classical
open OAI.HypercubeRamsey
open scoped BigOperators

open HypercubeRamsey.S04

private def diffSet {d : ℕ} (v u : CubeVertex d) : Finset (Fin d) :=
  Finset.univ.filter (fun i => u i ≠ v i)

private def vertexOfDiff {d : ℕ} (v : CubeVertex d) (s : Finset (Fin d)) : CubeVertex d :=
  fun i => if i ∈ s then !(v i) else v i

private def diffEquiv {d : ℕ} (v : CubeVertex d) : CubeVertex d ≃ Finset (Fin d) where
  toFun := diffSet v
  invFun := vertexOfDiff v
  left_inv := by
    intro u
    funext i
    by_cases hi : u i = v i
    · simp [vertexOfDiff, diffSet, hi]
    · have hmem : i ∈ diffSet v u := by simp [diffSet, hi]
      have hbool : v i = !(u i) := by
        cases hu : u i <;> cases hv : v i <;> simp_all
      simp [vertexOfDiff, hmem, hbool]
  right_inv := by
    intro s
    ext i
    by_cases hi : i ∈ s
    · simp [diffSet, vertexOfDiff, hi]
    · simp [diffSet, vertexOfDiff, hi]

private theorem diffSet_card {d : ℕ} (v u : CubeVertex d) :
    (diffSet v u).card = hammingDist u v := by
  simp [diffSet, hammingDist, ne_comm]

private def ballToSubsets {d r : ℕ} (v : CubeVertex d) :
    {u : CubeVertex d // hammingDist u v ≤ r} ≃ {s : Finset (Fin d) // s.card ≤ r} where
  toFun u := ⟨diffSet v u.1, by rw [diffSet_card]; exact u.2⟩
  invFun s := ⟨vertexOfDiff v s.1, by
    rw [← diffSet_card]
    simp [diffSet, vertexOfDiff]
    exact s.2⟩
  left_inv := by
    intro u
    apply Subtype.ext
    exact (diffEquiv v).left_inv u.1
  right_inv := by
    intro s
    apply Subtype.ext
    exact (diffEquiv v).right_inv s.1

private def smallSubsetFiberEquiv (d r : ℕ) (i : Fin (r + 1)) :
    {s : {s : Finset (Fin d) // s.card ≤ r} // (⟨s.1.card, by omega⟩ : Fin (r + 1)) = i} ≃
      {s : Finset (Fin d) // s.card = i.val} where
  toFun s := ⟨s.1.1, by
    have h := congrArg Fin.val s.2
    simpa using h⟩
  invFun s := ⟨⟨s.1, by rw [s.2]; omega⟩, by
    apply Fin.ext
    exact s.2⟩
  left_inv := by
    intro s
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro s
    apply Subtype.ext
    rfl

private def subsetsSmallEquiv (d r : ℕ) :
    {s : Finset (Fin d) // s.card ≤ r} ≃
      Σ i : Fin (r + 1), {s : Finset (Fin d) // s.card = i.val} := by
  let f : {s : Finset (Fin d) // s.card ≤ r} → Fin (r + 1) :=
    fun s => ⟨s.1.card, by omega⟩
  exact (Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight (smallSubsetFiberEquiv d r))

private theorem card_small_subsets (d r : ℕ) :
    Fintype.card {s : Finset (Fin d) // s.card ≤ r} =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  rw [Fintype.card_congr (subsetsSmallEquiv d r), Fintype.card_sigma]
  have hfiber (i : Fin (r + 1)) :
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Nat.choose d i.val := by
    let S : Finset (Finset (Fin d)) := Finset.univ.powersetCard i.val
    let e : {s : Finset (Fin d) // s.card = i.val} ≃ S :=
      { toFun := fun s => ⟨s.1, by
          rw [Finset.mem_powersetCard]
          exact ⟨Finset.subset_univ _, s.2⟩⟩
        invFun := fun s => ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
        left_inv := by intro s; apply Subtype.ext; rfl
        right_inv := by intro s; apply Subtype.ext; rfl }
    calc
      Fintype.card {s : Finset (Fin d) // s.card = i.val} = Fintype.card S := Fintype.card_congr e
      _ = S.card := Fintype.card_coe S
      _ = Nat.choose d i.val := by simp [S, Finset.card_powersetCard]
  simp_rw [hfiber]
  rw [← Fin.sum_univ_eq_sum_range]

private theorem hammingBall_card (d r : ℕ) (v : CubeVertex d) :
    (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card =
      ∑ i ∈ Finset.range (r + 1), Nat.choose d i := by
  classical
  have hcard : Fintype.card {u : CubeVertex d // hammingDist u v ≤ r} =
      (Finset.univ.filter (fun u : CubeVertex d => hammingDist u v ≤ r)).card := by
    simpa using (Fintype.card_subtype (fun u : CubeVertex d => hammingDist u v ≤ r))
  exact hcard.symm.trans ((Fintype.card_congr (ballToSubsets v)).trans (card_small_subsets d r))

theorem center_weight_sum_eq (β γ : ℝ) (n : ℕ) (c₃ : ℝ) (v : CubeVertex n) :
    ∑ c : Loc β γ n, (if _root_.hammingDist c.1 v ≤ radius β γ n then
      wc β γ n c₃ c else 0) =
      3 + (topH β γ n : ℝ) * lamH n * Real.exp (-(n : ℝ) ^ c₃) := by
  classical
  have hVnat : 0 < (hd β γ n).V := by
    change 0 < ∑ i ∈ Finset.range (radius β γ n + 1), n.choose i
    have hmem : 0 ∈ Finset.range (radius β γ n + 1) := by simp
    have hsum : 1 ≤ ∑ i ∈ Finset.range (radius β γ n + 1), n.choose i := by
      calc
        1 = n.choose 0 := by simp
        _ ≤ ∑ i ∈ Finset.range (radius β γ n + 1), n.choose i :=
          Finset.single_le_sum (s := Finset.range (radius β γ n + 1))
            (f := fun i => n.choose i) (fun i hi => Nat.zero_le _) hmem
    omega
  have hVpos : 0 < ((hd β γ n).V : ℝ) := by exact_mod_cast hVnat
  have hBall :
      (Finset.univ.filter (fun u : CubeVertex n =>
        _root_.hammingDist u v ≤ radius β γ n)).card = (hd β γ n).V := by
    calc
      _ = ∑ i ∈ Finset.range (radius β γ n + 1), Nat.choose n i :=
        hammingBall_card n (radius β γ n) v
      _ = (hd β γ n).V := by simp [hd, HDParams.V]
  have hsumBall (d : ℝ) :
      (∑ u : CubeVertex n, if _root_.hammingDist u v ≤ radius β γ n then d else 0) =
        (((hd β γ n).V : ℝ) * d) := by
    calc
      _ = ∑ u ∈ Finset.univ.filter (fun u : CubeVertex n =>
          _root_.hammingDist u v ≤ radius β γ n), d := by
            rw [← Finset.sum_filter]
      _ = ((hd β γ n).V : ℝ) * d := by simp [hBall]
  have hlevel (j : Fin (topH β γ n + 1)) :
      ∑ u : CubeVertex n,
          (if _root_.hammingDist u v ≤ radius β γ n then wc β γ n c₃ (u, j) else 0) =
        if j.val = 0 then 3 else lamH n * Real.exp (-(n : ℝ) ^ c₃) := by
    by_cases hj : j.val = 0
    · have hj0 : j = 0 := Fin.ext hj
      subst j
      simp only [wc, if_pos rfl]
      change (∑ u : CubeVertex n,
        if _root_.hammingDist u v ≤ radius β γ n then
          3 / ((hd β γ n).V : ℝ) else 0) = 3
      rw [hsumBall]
      field_simp [ne_of_gt hVpos]
    · simp only [wc, hj, if_false]
      rw [hsumBall]
      field_simp [ne_of_gt hVpos]
  have hsumLevels :
      (∑ j : Fin (topH β γ n + 1),
        (if j.val = 0 then 3 else lamH n * Real.exp (-(n : ℝ) ^ c₃))) =
          3 + (topH β γ n : ℝ) * lamH n * Real.exp (-(n : ℝ) ^ c₃) := by
    rw [Fin.sum_univ_succ]
    simp [Finset.sum_const, nsmul_eq_mul] <;> ring
  change ∑ c : CubeVertex n × Fin (topH β γ n + 1),
      (if _root_.hammingDist c.1 v ≤ radius β γ n then wc β γ n c₃ c else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hlevel]
  exact hsumLevels

theorem center_weight_budget_le {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (c₃ : ℝ) (x : Fin N)
    (hball : ∀ v : CubeVertex n,
      ∑ c : Loc β γ n, (if _root_.hammingDist c.1 v ≤ radius β γ n then
        wc β γ n c₃ c else 0) ≤ 4) :
    ∑ ck : Loc β γ n × Key β γ n,
      ((Finset.univ.filter fun a : EvenRole n =>
        key β γ n a.1 = ck.2 ∧ _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n).card : ℝ) *
          wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x ≤
      4 * ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x := by
  classical
  let roles (ck : Loc β γ n × Key β γ n) :=
    Finset.univ.filter fun a : EvenRole n =>
      key β γ n a.1 = ck.2 ∧ _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n
  have hcard (ck : Loc β γ n × Key β γ n) :
      (roles ck).card = ∑ a : EvenRole n,
        if key β γ n a.1 = ck.2 ∧
          _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then 1 else 0 := by
    dsimp [roles]
    rw [← Finset.sum_filter]
    simp
  have hEq :
      ∑ ck : Loc β γ n × Key β γ n,
        ((roles ck).card : ℝ) * wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x =
      ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x *
        ∑ c : Loc β γ n,
          (if _root_.hammingDist c.1 a.1 ≤ radius β γ n then wc β γ n c₃ c else 0) := by
    calc
      _ = ∑ ck : Loc β γ n × Key β γ n,
          (∑ a : EvenRole n,
            (if key β γ n a.1 = ck.2 ∧
              _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then 1 else 0) *
                (wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x)) := by
            apply Finset.sum_congr rfl
            intro ck hck
            rw [show ((roles ck).card : ℝ) = ∑ a : EvenRole n,
                (if key β γ n a.1 = ck.2 ∧
                  _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then (1 : ℝ) else 0) by
                    exact_mod_cast hcard ck]
            calc
              (∑ a : EvenRole n,
                (if key β γ n a.1 = ck.2 ∧
                  _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then 1 else 0)) *
                  wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x =
                (∑ a : EvenRole n,
                  (if key β γ n a.1 = ck.2 ∧
                    _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then 1 else 0)) *
                  (wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x) := by ring
              _ = ∑ a : EvenRole n,
                  (if key β γ n a.1 = ck.2 ∧
                    _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then 1 else 0) *
                    (wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x) := by rw [Finset.sum_mul]
      _ = ∑ a : EvenRole n, ∑ ck : Loc β γ n × Key β γ n,
          (if key β γ n a.1 = ck.2 ∧
            _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then 1 else 0) *
              (wc β γ n c₃ ck.1 * (M.μ (tag ck.2)).w x) := by
            rw [Finset.sum_comm]
      _ = ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x *
          ∑ c : Loc β γ n,
            (if _root_.hammingDist c.1 a.1 ≤ radius β γ n then wc β γ n c₃ c else 0) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Fintype.sum_prod_type]
            have hkey (c : Loc β γ n) :
                ∑ κ : Key β γ n,
                  (if key β γ n a.1 = κ ∧
                    _root_.hammingDist c.1 a.1 ≤ radius β γ n then 1 else 0) *
                      (wc β γ n c₃ c * (M.μ (tag κ)).w x) =
                  if _root_.hammingDist c.1 a.1 ≤ radius β γ n then
                  wc β γ n c₃ c * (M.μ (tag (key β γ n a.1))).w x else 0 := by
              by_cases hd : _root_.hammingDist c.1 a.1 ≤ radius β γ n
              · simp [hd, eq_comm, Finset.sum_ite_eq']
              · simp [hd]
            calc
              (∑ c : Loc β γ n, ∑ κ : Key β γ n,
                  (if key β γ n a.1 = κ ∧
                    _root_.hammingDist c.1 a.1 ≤ radius β γ n then 1 else 0) *
                      (wc β γ n c₃ c * (M.μ (tag κ)).w x)) =
                  ∑ c : Loc β γ n,
                    if _root_.hammingDist c.1 a.1 ≤ radius β γ n then
                      wc β γ n c₃ c * (M.μ (tag (key β γ n a.1))).w x else 0 := by
                        apply Finset.sum_congr rfl
                        intro c hc
                        exact hkey c
              _ = ∑ c, (M.μ (tag (key β γ n a.1))).w x *
                    (if _root_.hammingDist c.1 a.1 ≤ radius β γ n then wc β γ n c₃ c else 0) := by
                    apply Finset.sum_congr rfl
                    intro c hc
                    by_cases hd : _root_.hammingDist c.1 a.1 ≤ radius β γ n <;>
                      simp [hd, mul_comm]
              _ = (M.μ (tag (key β γ n a.1))).w x *
                    ∑ c : Loc β γ n,
                      (if _root_.hammingDist c.1 a.1 ≤ radius β γ n then
                        wc β γ n c₃ c else 0) := by rw [Finset.mul_sum]
              _ = _ := rfl
  rw [hEq]
  calc
    ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x *
        ∑ c : Loc β γ n,
          (if _root_.hammingDist c.1 a.1 ≤ radius β γ n then wc β γ n c₃ c else 0) ≤
        ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x * 4 := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hball a.1)
            ((M.μ (tag (key β γ n a.1))).nonneg x)
    _ = 4 * ∑ a : EvenRole n, (M.μ (tag (key β γ n a.1))).w x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring

noncomputable def pointMass {α : Type*} [Fintype α] [DecidableEq α] (a : α) : FinProb α where
  w x := if x = a then 1 else 0
  nonneg x := by split_ifs <;> norm_num
  sum_eq_one := by simp

noncomputable def pointXProf {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (xm : XMasks M tag) : XProf M tag := fun ck => pointMass (xm ck)

noncomputable def pointYProf {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ym : YMasks M tag) : YProf M tag := fun u => pointMass (ym u)

noncomputable def maskProfileLaw {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (q : XProf M tag) (q' : YProf M tag) :
    FinProb (XMasks M tag × YMasks M tag) :=
  (FinProb.pi q).prod (FinProb.pi q')

theorem pi_pointMass_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (x y : ∀ i, Ω i) :
    (FinProb.pi (fun i => pointMass (x i))).w y = if y = x then 1 else 0 := by
  classical
  change (∏ i, if y i = x i then (1 : ℝ) else 0) = if y = x then 1 else 0
  by_cases h : y = x
  · subst y
    simp
  · have hne : ∃ i, y i ≠ x i := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      exact hn i
    obtain ⟨i, hi⟩ := hne
    have hyx : y ≠ x := by
      intro hEq
      exact hi (congrFun hEq i)
    have hi0 : (if y i = x i then (1 : ℝ) else 0) = 0 := if_neg hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi0]
    simp [hyx]

theorem expect_prod {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (f : α × β → ℝ) :
    (P.prod Q).expect f = ∑ x, P.w x * Q.expect (fun y => f (x, y)) := by
  classical
  unfold FinProb.expect
  change (∑ z : α × β, (P.w z.1 * Q.w z.2) * f z) =
    ∑ x, P.w x * ∑ y, Q.w y * f (x, y)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ y, (P.w x * Q.w y) * f (x, y)) =
        ∑ y, P.w x * (Q.w y * f (x, y)) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = P.w x * ∑ y, Q.w y * f (x, y) := by rw [Finset.mul_sum]

theorem expect_weighted_sum {α Ω : Type*} [Fintype α] [Fintype Ω]
    (P : FinProb Ω) (w : α → ℝ) (f : α → Ω → ℝ) :
    P.expect (fun ω => ∑ a, w a * f a ω) = ∑ a, w a * P.expect (f a) := by
  classical
  unfold FinProb.expect
  calc
    (∑ ω, P.w ω * ∑ a, w a * f a ω) =
        ∑ ω, ∑ a, w a * (P.w ω * f a ω) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring
    _ = ∑ a, ∑ ω, w a * (P.w ω * f a ω) := by rw [Finset.sum_comm]
    _ = ∑ a, w a * ∑ ω, P.w ω * f a ω := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_sum]
    _ = ∑ a, w a * P.expect (f a) := rfl

theorem maskProfileLaw_point_weight {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (s t : XMasks M tag × YMasks M tag) :
    (maskProfileLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w t =
      if t = s then 1 else 0 := by
  classical
  rcases s with ⟨xm, ym⟩
  rcases t with ⟨xm', ym'⟩
  change (FinProb.pi (fun ck => pointMass (xm ck))).w xm' *
      (FinProb.pi (fun u => pointMass (ym u))).w ym' =
    if (xm', ym') = (xm, ym) then 1 else 0
  rw [pi_pointMass_weight xm xm', pi_pointMass_weight ym ym']
  by_cases hx : xm' = xm <;> by_cases hy : ym' = ym
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]
  · simp [hx, hy]

set_option maxHeartbeats 10000000 in
theorem prepLaw_expect_profile_average {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (q : XProf M tag) (q' : YProf M tag) (f : Prep M tag → ℝ) :
    (prepLaw M tag q q').expect f =
      ∑ s : XMasks M tag × YMasks M tag,
        (maskProfileLaw M tag q q').w s *
          (prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).expect f := by
  classical
  have hweight (ω : Prep M tag) :
      (prepLaw M tag q q').w ω =
        ∑ s : XMasks M tag × YMasks M tag,
          (maskProfileLaw M tag q q').w s *
            (prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w ω := by
    rcases ω with ⟨⟨⟨P, ⟨⟨xm, ym⟩, W⟩⟩, A⟩, τ⟩
    let s₀ : XMasks M tag × YMasks M tag := (xm, ym)
    have haux (qₓ : XProf M tag) (qᵧ : YProf M tag)
        (xm' : XMasks M tag) (ym' : YMasks M tag)
        (W' : Tuples β γ n N) :
        (auxLaw M tag qₓ qᵧ).w (((xm', ym'), W')) =
          (maskProfileLaw M tag qₓ qᵧ).w (xm', ym') * (tupleLaw M tag xm').w W' := by
      unfold auxLaw
      change ((FinProb.pi qₓ).prod (FinProb.pi qᵧ)).w (xm', ym') *
        (tupleLaw M tag xm').w W' =
          (maskProfileLaw M tag qₓ qᵧ).w (xm', ym') * (tupleLaw M tag xm').w W'
      rfl
    simp only [prepLaw, FinProb.prod]
    rw [haux q q' xm ym W]
    simp_rw [haux]
    have hpoint : ∀ s : XMasks M tag × YMasks M tag,
        (maskProfileLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w s₀ =
          if s₀ = s then 1 else 0 :=
      fun s => maskProfileLaw_point_weight M tag s s₀
    have hpoint' (s : XMasks M tag × YMasks M tag) :
        (maskProfileLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w s₀ =
          if s = s₀ then 1 else 0 := by
      by_cases hs : s = s₀
      · subst s
        simpa using hpoint s₀
      · have hs' : s₀ ≠ s := fun h => hs h.symm
        simpa [hs, hs'] using hpoint s
    let K := (hd β γ n).posLaw.w P * (tupleLaw M tag xm).w W *
      (hd β γ n).actLaw.w A * (hd β γ n).tieLaw.w τ
    have hcollapse :
        (∑ s : XMasks M tag × YMasks M tag,
          (maskProfileLaw M tag q q').w s *
            ((maskProfileLaw M tag (pointXProf M tag s.1)
              (pointYProf M tag s.2)).w s₀ * K)) =
          (maskProfileLaw M tag q q').w s₀ * K := by
      calc
        _ = ∑ s, if s = s₀ then (maskProfileLaw M tag q q').w s * K else 0 := by
              apply Finset.sum_congr rfl
              intro s hs
              rw [hpoint' s]
              by_cases heq : s = s₀
              · simp [heq]
              · simp [heq]
        _ = (maskProfileLaw M tag q q').w s₀ * K := by
              rw [Finset.sum_eq_single s₀]
              · simp
              · intro s hs hne
                simp [hne]
              · simp
    calc
      _ = (maskProfileLaw M tag q q').w s₀ * K := by
        dsimp [K, s₀]
        ring
      _ = ∑ s : XMasks M tag × YMasks M tag,
          (maskProfileLaw M tag q q').w s *
            ((maskProfileLaw M tag (pointXProf M tag s.1)
              (pointYProf M tag s.2)).w s₀ * K) := hcollapse.symm
      _ = ∑ s : XMasks M tag × YMasks M tag,
          (maskProfileLaw M tag q q').w s *
            ((((hd β γ n).posLaw.w P *
              ((maskProfileLaw M tag (pointXProf M tag s.1)
                (pointYProf M tag s.2)).w (xm, ym) * (tupleLaw M tag xm).w W)) *
              (hd β γ n).actLaw.w A) * (hd β γ n).tieLaw.w τ) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
  unfold FinProb.expect
  rw [show (fun ω => (prepLaw M tag q q').w ω * f ω) =
      (fun ω => (∑ s : XMasks M tag × YMasks M tag,
        (maskProfileLaw M tag q q').w s *
          (prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w ω) * f ω) by
        funext ω
        rw [hweight]]
  calc
    (∑ ω, (∑ s : XMasks M tag × YMasks M tag,
        (maskProfileLaw M tag q q').w s *
          (prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w ω) * f ω) =
        ∑ ω, ∑ s : XMasks M tag × YMasks M tag,
          (maskProfileLaw M tag q q').w s *
            ((prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w ω * f ω) := by
          apply Finset.sum_congr rfl
          intro ω hω
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s hs
          ring
    _ = ∑ s : XMasks M tag × YMasks M tag, ∑ ω,
          (maskProfileLaw M tag q q').w s *
            ((prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).w ω * f ω) := by
          rw [Finset.sum_comm]
    _ = ∑ s : XMasks M tag × YMasks M tag,
          (maskProfileLaw M tag q q').w s *
            (prepLaw M tag (pointXProf M tag s.1) (pointYProf M tag s.2)).expect f := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [← Finset.mul_sum]
          rfl

noncomputable def profileSplitEquiv {ι : Type*} {A : ι → Type*} (j : ι) :
    (∀ i, A i) ≃ A j × (∀ i : {i // i ≠ j}, A i.1) where
  toFun σ := (σ j, fun i => σ i.1)
  invFun z i := if h : i = j then h.symm ▸ z.1 else z.2 ⟨i, h⟩
  left_inv σ := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]
  right_inv z := by
    rcases z with ⟨a, τ⟩
    apply Prod.ext
    · simp
    · funext i
      cases i with
      | mk k hk => simp [hk]

theorem pi_expect_update_split_dep {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (Q : ∀ i, FinProb (A i)) (j : ι) (R : FinProb (A j))
    (f : (∀ i, A i) → ℝ) :
    (FinProb.pi (Function.update Q j R)).expect f =
      ∑ a, R.w a *
        (FinProb.pi (fun i : {i // i ≠ j} => Q i.1)).expect
          (fun τ => f ((profileSplitEquiv j).symm (a, τ))) := by
  classical
  let O := {i : ι // i ≠ j}
  let e : (∀ i, A i) ≃ A j × (∀ i : O, A i.1) := profileSplitEquiv j
  let P₀ : (i : O) → FinProb (A i.1) := fun i => Q i.1
  have heval (a : A j) (τ : ∀ i : O, A i.1) : (e.symm (a, τ)) j = a := by
    simp [e, profileSplitEquiv]
  have hevalO (a : A j) (τ : ∀ i : O, A i.1) (i : O) :
      (e.symm (a, τ)) i.1 = τ i := by
    cases i with
    | mk k hk => simp [e, profileSplitEquiv, hk]
  have hprod (a : A j) (τ : ∀ i : O, A i.1) :
      (∏ i, (Function.update Q j R i).w ((e.symm (a, τ)) i)) =
        R.w a * ∏ i : O, (Q i.1).w (τ i) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne
      (fun i => (Function.update Q j R i).w ((e.symm (a, τ)) i)) j]
    rw [show (Function.update Q j R j).w ((e.symm (a, τ)) j) = R.w a by
      simp [heval a τ]]
    congr 1
    apply Fintype.prod_congr
    intro i
    rw [Function.update_of_ne i.2, hevalO a τ i]
  simp only [FinProb.expect, FinProb.pi]
  rw [← Equiv.sum_comp e.symm
    (fun σ => (∏ i, (Function.update Q j R i).w (σ i)) * f σ)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [hprod]
  ring

def profileSumEquiv {α β : Type*} {A : Sum α β → Type*} :
    (∀ i, A i) ≃ (∀ a, A (.inl a)) × (∀ b, A (.inr b)) where
  toFun σ := (fun a => σ (.inl a), fun b => σ (.inr b))
  invFun q i := match i with
    | .inl a => q.1 a
    | .inr b => q.2 b
  left_inv σ := by
    funext i
    cases i <;> rfl
  right_inv q := by
    cases q with
    | mk ql qr => exact Prod.ext (by funext a; rfl) (by funext b; rfl)

theorem pi_sum_expect {α β : Type*} [Fintype α] [Fintype β]
    {A : Sum α β → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (P : ∀ i, FinProb (A i)) (f : (∀ i, A i) → ℝ) :
    (FinProb.pi P).expect f =
      ((FinProb.pi (fun a => P (.inl a))).prod (FinProb.pi (fun b => P (.inr b)))).expect
        (fun q => f ((profileSumEquiv (A := A)).symm q)) := by
  classical
  let e := profileSumEquiv (A := A)
  simp only [FinProb.expect, FinProb.pi, FinProb.prod]
  rw [← Equiv.sum_comp e.symm
    (fun σ => (∏ i, (P i).w (σ i)) * f σ)]
  apply Finset.sum_congr rfl
  intro q hq
  rcases q with ⟨ql, qr⟩
  simp only [e, profileSumEquiv]
  rw [Fintype.prod_sum_type]
  simp

abbrev ProfilePlayers (β γ : ℝ) (n : ℕ) :=
  Sum (Loc β γ n × Key β γ n) (OddRole n)

abbrev ProfileActions {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) :
    ProfilePlayers β γ n → Type
  | .inl ck => Mask (M.μ (tag ck.2))
  | .inr u => Mask (M.ν (tag (key β γ n u.1)))

noncomputable instance instFintypeProfileActions {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (j : ProfilePlayers β γ n) : Fintype (ProfileActions M tag j) := by
  cases j with
  | inl ck => exact inferInstance
  | inr u => exact inferInstance

noncomputable instance instDecidableEqProfileActions {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (j : ProfilePlayers β γ n) : DecidableEq (ProfileActions M tag j) := by
  classical
  cases j with
  | inl ck => exact Classical.decEq _
  | inr u => exact Classical.decEq _

theorem topScale_le_product (n : ℕ) (σ ζ : ℝ)
    (hT : 1 ≤ ⌈(n : ℝ) ^ (1 - ζ)⌉₊) :
    HypercubeRamsey.topScale n σ ζ ≤
      (max 2 ⌈(n : ℝ) ^ σ⌉₊) * ⌈(n : ℝ) ^ (1 - ζ)⌉₊ *
        (max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊) := by
  classical
  let R : ℕ := max 1 ⌈Real.log (n : ℝ) ^ 2⌉₊
  let M : ℕ := max 2 ⌈(n : ℝ) ^ σ⌉₊
  let T : ℕ := ⌈(n : ℝ) ^ (1 - ζ)⌉₊
  have hR : 1 ≤ R := by dsimp [R]; exact le_max_left _ _
  have hM : 2 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hT' : 1 ≤ T := by simpa [T] using hT
  have hexists : ∃ i : ℕ, T ≤ M ^ i * R := by
    induction T with
    | zero => exact ⟨0, by simp⟩
    | succ t ih =>
      obtain ⟨i, hi⟩ := ih
      let x := M ^ i * R
      have hx0 : x ≠ 0 := by
        dsimp [x]
        exact Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (by omega)
      have hx : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
      refine ⟨i + 1, ?_⟩
      calc
        t + 1 ≤ x + 1 := Nat.succ_le_succ hi
        _ ≤ 2 * x := by omega
        _ ≤ M * x := Nat.mul_le_mul_right x hM
        _ = M ^ (i + 1) * R := by dsimp [x]; rw [pow_succ]; ring
  let i := Nat.find hexists
  have hiSpec : T ≤ M ^ i * R := Nat.find_spec hexists
  have hbound : M ^ i * R ≤ M * T * R := by
    by_cases hi0 : i = 0
    · rw [hi0, pow_zero, one_mul]
      have hMT : 1 ≤ M * T := by
        calc
          1 = 1 * 1 := by norm_num
          _ ≤ M * T := Nat.mul_le_mul (by omega) hT'
      calc
        R = 1 * R := by simp
        _ ≤ (M * T) * R := Nat.mul_le_mul_right R hMT
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hprev : M ^ (i - 1) * R < T := by
        have hiPred : i - 1 < Nat.find hexists := by dsimp [i]; omega
        have hnot : ¬ T ≤ M ^ (i - 1) * R := Nat.find_min hexists hiPred
        exact Nat.lt_of_not_ge hnot
      have hpow : M ^ i * R = M * (M ^ (i - 1) * R) := by
        have hi' : i = (i - 1) + 1 := by omega
        have hpowEq : M ^ i = M ^ ((i - 1) + 1) := congrArg (fun k : ℕ => M ^ k) hi'
        calc
          M ^ i * R = M ^ ((i - 1) + 1) * R := by rw [hpowEq]
          _ = (M ^ (i - 1) * M) * R := by rw [pow_succ]
          _ = M * (M ^ (i - 1) * R) := by ac_rfl
      rw [hpow]
      calc
        M * (M ^ (i - 1) * R) ≤ M * T := Nat.mul_le_mul_left M hprev.le
        _ ≤ (M * T) * R := by
          calc
            M * T = (M * T) * 1 := by simp
            _ ≤ (M * T) * R := Nat.mul_le_mul_left (M * T) hR
  change M ^ Nat.find hexists * R ≤ M * T * R
  exact hbound

theorem pr_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → Prop) :
    (P.prod Q).pr (fun z => A z.1) = P.pr A := by
  classical
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hA : A x
  · simp [hA, ← Finset.mul_sum, Q.sum_eq_one]
  · simp [hA]

theorem pr_prod_cond {α β : Type*} [Fintype α] [Fintype β]
    (P : FinProb α) (Q : FinProb β) (A : α → β → Prop) :
    (P.prod Q).pr (fun z => A z.1 z.2) =
      ∑ x, P.w x * Q.pr (A x) := by
  classical
  unfold FinProb.pr FinProb.prod
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ y, if A x y then P.w x * Q.w y else 0) =
        ∑ y, P.w x * (if A x y then Q.w y else 0) := by
          apply Finset.sum_congr rfl
          intro y hy
          by_cases h : A x y <;> simp [h]
    _ = P.w x * (∑ y, if A x y then Q.w y else 0) := by rw [Finset.mul_sum]

theorem pr_prod_assoc {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : FinProb α) (Q : FinProb β) (R : FinProb γ)
    (A : (α × β) × γ → Prop) :
    ((P.prod Q).prod R).pr A =
      (P.prod (Q.prod R)).pr (fun z => A ((z.1, z.2.1), z.2.2)) := by
  classical
  unfold FinProb.pr FinProb.prod
  let e : ((α × β) × γ) ≃ α × (β × γ) := Equiv.prodAssoc _ _ _
  change
    (∑ z : (α × β) × γ,
      if A z then (P.w z.1.1 * Q.w z.1.2) * R.w z.2 else 0) =
    ∑ z : α × (β × γ),
      if A ((z.1, z.2.1), z.2.2) then P.w z.1 * (Q.w z.2.1 * R.w z.2.2) else 0
  exact Fintype.sum_equiv e _ _ (by intro z; simp [e, mul_assoc])

theorem pr_prod_scale {α β : Type*} [Fintype α] [Fintype β]
    (P P' : FinProb α) (Q : FinProb β) (c : ℝ) (hc : 0 ≤ c)
    (A B : α × β → Prop)
    (hAB : ∀ z, A z → B z)
    (hw : ∀ x, (∃ y, A (x, y)) → P.w x ≤ c * P'.w x) :
    (P.prod Q).pr A ≤ c * (P'.prod Q).pr B := by
  classical
  change (P.prod Q).pr (fun z => A (z.1, z.2)) ≤
    c * (P'.prod Q).pr (fun z => B (z.1, z.2))
  rw [pr_prod_cond P Q (fun x y => A (x, y)),
    pr_prod_cond P' Q (fun x y => B (x, y))]
  calc
    (∑ x, P.w x * Q.pr (fun y => A (x, y))) ≤
        ∑ x, (c * P'.w x) * Q.pr (fun y => B (x, y)) := by
          apply Finset.sum_le_sum
          intro x hx
          by_cases hA : ∃ y, A (x, y)
          · have hweight := hw x hA
            have hprob := HypercubeRamsey.S04.pr_mono Q
              (fun y h => hAB (x, y) h)
            have hprob0 := HypercubeRamsey.S04.pr_nonneg Q (fun y => A (x, y))
            calc
              P.w x * Q.pr (fun y => A (x, y)) ≤
                  (c * P'.w x) * Q.pr (fun y => A (x, y)) :=
                    mul_le_mul_of_nonneg_right hweight hprob0
              _ ≤ (c * P'.w x) * Q.pr (fun y => B (x, y)) :=
                    mul_le_mul_of_nonneg_left hprob (mul_nonneg hc (P'.nonneg x))
          · have hz : Q.pr (fun y => A (x, y)) = 0 := by
              unfold FinProb.pr
              apply Finset.sum_eq_zero
              intro y hy
              have hfalse : ¬ A (x, y) := fun h => hA ⟨y, h⟩
              simp [hfalse]
            rw [hz]
            simpa using mul_nonneg (mul_nonneg hc (P'.nonneg x))
              (HypercubeRamsey.S04.pr_nonneg Q (fun y => B (x, y)))
    _ = c * (∑ x, P'.w x * Q.pr (fun y => B (x, y))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring

theorem pos_weight_le_forced {β γ : ℝ} {n : ℕ}
    (c : HypercubeRamsey.S04.Loc β γ n)
    (P : HypercubeRamsey.S04.Pos β γ n) (hP : P c = true) :
    (HypercubeRamsey.S04.hd β γ n).posLaw.w P ≤
      ((HypercubeRamsey.S04.hd β γ n).lam /
        ((HypercubeRamsey.S04.hd β γ n).V : ℝ)) *
        ((HypercubeRamsey.S04.hd β γ n).posLawForced (some c)).w P := by
  classical
  let p := HypercubeRamsey.S04.hd β γ n
  let q : ℝ := p.lam / (p.V : ℝ)
  have hq : 0 ≤ q := by
    dsimp [q, p, HypercubeRamsey.S04.hd, HypercubeRamsey.S04.lamH]
    positivity
  have hclamp : max 0 (min q 1) ≤ q := max_le hq (min_le_left q 1)
  unfold HDParams.posLaw HDParams.posLawForced FinProb.pi
  change (∏ ℓ, (FinProb.bernoulli q).w (P ℓ)) ≤
    q * ∏ ℓ, (if some c = some ℓ then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P ℓ)
  rw [← Finset.mul_prod_erase Finset.univ
    (fun ℓ => (FinProb.bernoulli q).w (P ℓ)) (Finset.mem_univ c)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun ℓ => (if some c = some ℓ then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P ℓ))
    (Finset.mem_univ c)]
  have hrest :
      (∏ ℓ ∈ Finset.univ.erase c,
          (FinProb.bernoulli q).w (P ℓ)) =
        ∏ ℓ ∈ Finset.univ.erase c,
          (if some c = some ℓ then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hne : ℓ ≠ c := Finset.ne_of_mem_erase hℓ
    simp only [Option.some.injEq, hne.symm, if_false]
  rw [hrest]
  let rest : ℝ := ∏ ℓ ∈ Finset.univ.erase c,
      (if some c = some ℓ then FinProb.bernoulli 1 else FinProb.bernoulli q).w (P ℓ)
  have hrest0 : 0 ≤ rest := by
    dsimp [rest]
    exact Finset.prod_nonneg fun ℓ hℓ => by
      split_ifs <;> exact (FinProb.bernoulli _).nonneg _
  have htrue : (FinProb.bernoulli q).w true = max 0 (min q 1) := by
    simp [FinProb.bernoulli]
  have hforced : (FinProb.bernoulli 1).w true = 1 := by
    simp [FinProb.bernoulli]
  rw [hP]
  rw [if_pos (show some c = some c from rfl)]
  change (FinProb.bernoulli q).w true * rest ≤
    q * ((FinProb.bernoulli 1).w true * rest)
  rw [htrue, hforced]
  calc
    max 0 (min q 1) * rest ≤ q * rest := mul_le_mul_of_nonneg_right hclamp hrest0
    _ = q * (1 * rest) := by ring

theorem selection_mem_height {p : HDParams} (Sites : p.Sites)
    (P A : p.Loc → Bool) (E : p.EligMap) (τ : p.Ties)
    (v : CubeVertex p.d) (c : p.Loc)
    (hsel : p.selection Sites P A E τ v = some c) :
    ∃ j : Fin (p.H + 1), j.val = p.height Sites P A E p.Rlong v ∧
      c ∈ E v j ∧ A c = true := by
  classical
  let j := p.height Sites P A E p.Rlong v
  have hj : j < p.H := by
    by_contra hnot
    have hge : p.H ≤ j := by omega
    simp [j, HDParams.selection, HDParams.selectionAt, hge] at hsel
  let j' : Fin (p.H + 1) := ⟨j, by omega⟩
  let active : Finset p.Loc := (E v j').filter (fun ℓ => A ℓ = true)
  let priorities := active.image (fun ℓ => p.priority τ (v, j') ℓ)
  have hbad : ¬ p.Bad P A E v j' := by
    by_contra h
    simp [j, j', HDParams.selection, HDParams.selectionAt, hj, h, active, priorities] at hsel
  have hne : priorities.Nonempty := by
    by_contra h
    simp [j, j', HDParams.selection, HDParams.selectionAt, hj, hbad, h, active, priorities] at hsel
  have hchosen : Classical.choose (Finset.mem_image.mp (Finset.min'_mem priorities hne)) = c := by
    simpa [j, j', HDParams.selection, HDParams.selectionAt, hj, hbad, hne, active, priorities] using hsel
  have hspec := Classical.choose_spec (Finset.mem_image.mp (Finset.min'_mem priorities hne))
  rw [hchosen] at hspec
  have hactive : c ∈ active := hspec.1
  have hfiltered := Finset.mem_filter.mp hactive
  exact ⟨j', rfl, hfiltered.1, hfiltered.2⟩

theorem selection_radius {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (ω : Prep M tag) (v : CubeVertex n) (c : Loc β γ n)
    (hsel : sel M tag ω v = some c) :
    _root_.hammingDist c.1 v ≤ radius β γ n := by
  classical
  have hsel' : (hd β γ n).selection (evenSites n) (ppos ω) (pact ω)
      (elig M tag (ppos ω) (paux ω)) (pties ω) v = some c := by
    simpa [sel] using hsel
  obtain ⟨j, _, hmem, _⟩ := selection_mem_height
    (p := hd β γ n) (evenSites n) (ppos ω) (pact ω) (elig M tag (ppos ω) (paux ω))
    (pties ω) v c hsel'
  unfold elig at hmem
  rcases Finset.mem_sdiff.mp hmem with ⟨hbase, _⟩
  exact (Finset.mem_filter.mp hbase).2.2.2

theorem rawEven_center_decomp {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (q : XProf M tag) (q' : YProf M tag) (a : EvenRole n) (x : Fin N) :
    ∑ ck : Loc β γ n × Key β γ n,
      (if key β γ n a.1 = ck.2 ∧
          _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n then
        (prepLaw M tag q q').expect (fun ω =>
          if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)
      else 0) = rawEven M tag q q' a x := by
  classical
  let P := prepLaw M tag q q'
  let inRange (ck : Loc β γ n × Key β γ n) : Prop :=
    key β γ n a.1 = ck.2 ∧ _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n
  let part (ck : Loc β γ n × Key β γ n) (ω : Prep M tag) : ℝ :=
    if inRange ck then
      if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0
    else 0
  let weight (ck : Loc β γ n × Key β γ n) : ℝ := if inRange ck then 1 else 0
  let unweightedPart (ck : Loc β γ n × Key β γ n) (ω : Prep M tag) : ℝ :=
    if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0
  have hpoint (ω : Prep M tag) : ∑ ck, part ck ω = evenMean M tag ω a x := by
    by_cases hsel : sel M tag ω a.1 = none
    · have hmean : evenMean M tag ω a x = 0 := by
        unfold evenMean
        rw [show (fun f => evenRowAt M tag ω a (nbrLabels f a) x) =
          (fun _ => 0) by funext f; simp [evenRowAt, hsel]]
        exact FinProb.expect_const _ _
      simp [part, inRange, hsel, hmean]
    · obtain ⟨c, hc⟩ : ∃ c, sel M tag ω a.1 = some c := by
        cases h : sel M tag ω a.1 with
        | none => exact False.elim (hsel h)
        | some c => exact ⟨c, rfl⟩
      have hnear := selection_radius M tag ω a.1 c hc
      let ck₀ : Loc β γ n × Key β γ n := (c, key β γ n a.1)
      have hterm : part ck₀ ω = evenMean M tag ω a x := by
        simp [part, inRange, ck₀, hc, hnear]
      have hzero (ck : Loc β γ n × Key β γ n) (hck : ck ≠ ck₀) : part ck ω = 0 := by
        by_cases hk : inRange ck
        · by_cases hselck : sel M tag ω a.1 = some ck.1
          · have hloc : ck.1 = c := (Option.some.inj (hc.symm.trans hselck)).symm
            have hkey : ck.2 = key β γ n a.1 := hk.1.symm
            have hEq : ck = ck₀ := by
              apply Prod.ext hloc hkey
            exact False.elim (hck hEq)
          · change (if inRange ck then
              (if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) else 0) = 0
            simp [hk, hselck]
        · simp [part, inRange, hk]
      rw [Finset.sum_eq_single ck₀]
      · simpa [hterm]
      · intro ck hck hne
        exact hzero ck hne
      · simp [ck₀]
  have hmix :
      (P.expect fun ω => ∑ ck, part ck ω) =
        ∑ ck, (if inRange ck then P.expect (fun ω =>
          if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) else 0) := by
    have hsum (ω : Prep M tag) :
        (∑ ck, part ck ω) = ∑ ck, weight ck * unweightedPart ck ω := by
      apply Finset.sum_congr rfl
      intro ck hck
      by_cases hr : inRange ck <;> simp [part, weight, unweightedPart, hr]
    calc
      P.expect (fun ω => ∑ ck, part ck ω) =
          P.expect (fun ω => ∑ ck, weight ck * unweightedPart ck ω) := by
            congr 1
            funext ω
            exact hsum ω
      _ = ∑ ck, weight ck * P.expect (unweightedPart ck) :=
            expect_weighted_sum P weight unweightedPart
      _ = ∑ ck, if inRange ck then P.expect (unweightedPart ck) else 0 := by
            apply Finset.sum_congr rfl
            intro ck hck
            by_cases hr : inRange ck <;> simp [weight, hr]
  calc
    (∑ ck : Loc β γ n × Key β γ n,
        (if inRange ck then P.expect (fun ω =>
          if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) else 0)) =
        P.expect (fun ω => ∑ ck, part ck ω) := hmix.symm
    _ = P.expect (fun ω => evenMean M tag ω a x) := by
          congr 1
          funext ω
          exact hpoint ω
    _ = rawEven M tag q q' a x := rfl

theorem exists_low_price_mask {N : ℕ} (μ : Law N) (price : Fin N → ℝ)
    (hprice : ∀ x, 0 ≤ price x) :
    ∃ S : Mask μ, ∀ x ∈ S.1, price x ≤ 2 * ∑ y, μ.w y * price y := by
  classical
  let avg : ℝ := ∑ y, μ.w y * price y
  have havg : 0 ≤ avg := by
    dsimp [avg]
    exact Finset.sum_nonneg fun y hy => mul_nonneg (μ.nonneg y) (hprice y)
  let S : Finset (Fin N) := Finset.univ.filter fun x =>
    μ.w x ≠ 0 ∧ price x ≤ 2 * avg
  have hmassEq : (∑ x ∈ S, μ.w x) = μ.pr (fun x => price x ≤ 2 * avg) := by
    classical
    unfold S
    rw [Finset.sum_filter]
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hp : price x ≤ 2 * avg
    · by_cases hw : μ.w x = 0 <;> simp [hp, hw]
    · simp [hp]
  have hgood : 1 / 2 ≤ μ.pr (fun x => price x ≤ 2 * avg) := by
    by_cases havgPos : 0 < avg
    · have hmark := FinProb.markov μ price (2 * avg) hprice (by positivity)
      have hlarge : μ.pr (fun x => 2 * avg < price x) ≤ 1 / 2 := by
        calc
          μ.pr (fun x => 2 * avg < price x) ≤ μ.pr (fun x => 2 * avg ≤ price x) :=
            HypercubeRamsey.S04.pr_mono μ
              (A := fun x => 2 * avg < price x)
              (B := fun x => 2 * avg ≤ price x)
              (by intro x hx; linarith)
          _ ≤ μ.expect price / (2 * avg) := hmark
          _ = 1 / 2 := by
            rw [show μ.expect price = avg by rfl]
            field_simp [ne_of_gt havgPos]
      have hcomp := HypercubeRamsey.S04.pr_add_pr_not μ (fun x => price x ≤ 2 * avg)
      have hnot : μ.pr (fun x => ¬ price x ≤ 2 * avg) ≤ 1 / 2 := by
        simpa [not_le] using hlarge
      linarith
    · have havgZero : avg = 0 := le_antisymm (le_of_not_gt havgPos) havg
      have hnot : μ.pr (fun x => ¬ price x ≤ 0) = 0 := by
        unfold FinProb.pr
        apply Finset.sum_eq_zero
        intro x hx
        by_cases hw : μ.w x = 0
        · simp [hw]
        · have hterm : μ.w x * price x ≤ avg := by
            dsimp [avg]
            exact Finset.single_le_sum
              (fun y hy => mul_nonneg (μ.nonneg y) (hprice y)) (Finset.mem_univ x)
          have hprod : μ.w x * price x = 0 := by
            rw [havgZero] at hterm
            exact le_antisymm hterm (mul_nonneg (μ.nonneg x) (hprice x))
          have hμ : 0 < μ.w x := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hw)
          have hpzero : price x = 0 := by
            by_contra hne
            have hp : 0 < price x := lt_of_le_of_ne (hprice x) (Ne.symm hne)
            exact (ne_of_gt (mul_pos hμ hp)) hprod
          simp [hpzero]
      have hcomp := HypercubeRamsey.S04.pr_add_pr_not μ (fun x => price x ≤ 0)
      rw [hnot] at hcomp
      have hle : μ.pr (fun x => price x ≤ 0) ≤ μ.pr (fun x => price x ≤ 2 * avg) := by
        apply HypercubeRamsey.S04.pr_mono
        intro x hx
        simpa [havgZero] using hx
      linarith
  refine ⟨⟨S, ?_⟩, ?_⟩
  · constructor
    · intro x hx
      exact (Finset.mem_filter.mp hx).2.1
    · rw [hmassEq]
      exact hgood
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.2

theorem prepLaw_point_masks {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (xm : XMasks M tag) (ym : YMasks M tag) (ω : Prep M tag)
    (hω : (prepLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)).w ω ≠ 0) :
    axm (paux ω) = xm ∧ aym (paux ω) = ym := by
  classical
  rcases ω with ⟨⟨⟨P, ⟨⟨xm', ym'⟩, W⟩⟩, A⟩, τ⟩
  have haux :
      (auxLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)).w (((xm', ym'), W)) ≠ 0 := by
    intro hz
    apply hω
    simp [prepLaw, FinProb.prod, hz]
  have hmask :
      (maskProfileLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)).w (xm', ym') ≠ 0 := by
    intro hz
    apply haux
    change (maskProfileLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)).w
        (xm', ym') * (tupleLaw M tag xm').w W = 0
    rw [hz]
    simp
  have hxm : (FinProb.pi (pointXProf M tag xm)).w xm' ≠ 0 := by
    intro hz
    apply hmask
    change (FinProb.pi (pointXProf M tag xm)).w xm' *
      (FinProb.pi (pointYProf M tag ym)).w ym' = 0
    rw [hz]
    simp
  have hym : (FinProb.pi (pointYProf M tag ym)).w ym' ≠ 0 := by
    intro hz
    apply hmask
    change (FinProb.pi (pointXProf M tag xm)).w xm' *
      (FinProb.pi (pointYProf M tag ym)).w ym' = 0
    rw [hz]
    simp
  change (FinProb.pi (fun ck => pointMass (xm ck))).w xm' ≠ 0 at hxm
  change (FinProb.pi (fun u => pointMass (ym u))).w ym' ≠ 0 at hym
  rw [pi_pointMass_weight xm xm'] at hxm
  rw [pi_pointMass_weight ym ym'] at hym
  have hxm' : xm' = xm := by
    by_contra hne
    simp [hne] at hxm
  have hym' : ym' = ym := by
    by_contra hne
    simp [hne] at hym
  exact ⟨hxm', hym'⟩

theorem law_restrict_support {N : ℕ} (μ : Law N) (S : Finset (Fin N))
    (hmass : 0 < ∑ x ∈ S, μ.w x) (y : Fin N)
    (hy : (μ.restrict S hmass).w y ≠ 0) : y ∈ S := by
  by_contra hnot
  simp [Law.restrict, hnot] at hy

theorem law_restrict_source {N : ℕ} (μ : Law N) (S : Finset (Fin N))
    (hmass : 0 < ∑ x ∈ S, μ.w x) (y : Fin N)
    (hy : (μ.restrict S hmass).w y ≠ 0) : μ.w y ≠ 0 := by
  by_contra hzero
  simp [Law.restrict, hzero] at hy

theorem maskLaw_support {N : ℕ} {μ : Law N} (S : Mask μ) (y : Fin N)
    (hy : (maskLaw S).w y ≠ 0) : y ∈ S.1 := by
  exact law_restrict_support μ S.1 (mask_mass_pos S) y (by simpa [maskLaw] using hy)

theorem odd_price_pure_le {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (xm : XMasks M tag) (ym : YMasks M tag) (u : OddRole n)
    (price : Fin N → ℝ) (hprice : ∀ y, 0 ≤ price y)
    (hlow : ∀ y ∈ (ym u).1,
      price y ≤ 2 * ∑ z, (M.ν (tag (key β γ n u.1))).w z * price z) :
    ∑ y, price y *
        (prepLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)).expect
          (fun ω => oddRow M tag ω u y) ≤
      2 * ∑ z, (M.ν (tag (key β γ n u.1))).w z * price z := by
  classical
  let P := prepLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)
  let avg := ∑ z, (M.ν (tag (key β γ n u.1))).w z * price z
  have havg : 0 ≤ avg := by
    dsimp [avg]
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg ((M.ν (tag (key β γ n u.1))).nonneg z) (by
        exact hprice z)
  have hrow0 (ω : Prep M tag) (y : Fin N) : 0 ≤ oddRow M tag ω u y := by
    unfold oddRow
    split_ifs with h
    · exact (oddDraw M tag ω u).nonneg y
    · exact le_rfl
  have hpoint (ω : Prep M tag) (hω : P.w ω ≠ 0) :
      ∑ y, price y * oddRow M tag ω u y ≤ 2 * avg := by
    have hmask := prepLaw_point_masks M tag xm ym ω hω
    by_cases hodd : OddOK M tag ω u
    · have htotal : ∑ y, oddRow M tag ω u y = 1 := by
        simpa [oddRow, hodd] using (oddDraw M tag ω u).sum_eq_one
      have hsupp (y : Fin N) (hy : oddRow M tag ω u y ≠ 0) : y ∈ (ym u).1 := by
        have hdraw : (oddDraw M tag ω u).w y ≠ 0 := by simpa [oddRow, hodd] using hy
        have hsource : (maskLaw (aym (paux ω) u)).w y ≠ 0 := by
          by_contra hz
          apply hdraw
          simp [oddDraw, hodd, FinProb.cond, hz]
        have hmem := maskLaw_support (aym (paux ω) u) y hsource
        have hmasku : aym (paux ω) u = ym u := congrFun hmask.2 u
        simpa [hmasku] using hmem
      have hreplace :
          (∑ y, price y * oddRow M tag ω u y) =
            ∑ y, if y ∈ (ym u).1 then price y * oddRow M tag ω u y else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hmem : y ∈ (ym u).1
        · simp [hmem]
        · have hz : oddRow M tag ω u y = 0 := by
            by_contra hne
            exact hmem (hsupp y hne)
          simp [hmem, hz]
      rw [hreplace]
      calc
        (∑ y, if y ∈ (ym u).1 then price y * oddRow M tag ω u y else 0) ≤
            ∑ y, 2 * avg * oddRow M tag ω u y := by
              apply Finset.sum_le_sum
              intro y hy
              by_cases hmem : y ∈ (ym u).1
              · simp only [if_pos hmem]
                exact mul_le_mul_of_nonneg_right (hlow y hmem) (hrow0 ω y)
              · simp only [if_neg hmem]
                exact mul_nonneg (mul_nonneg (by norm_num) havg) (hrow0 ω y)
        _ = 2 * avg := by rw [← Finset.mul_sum, htotal]; ring
    · have hzero : ∑ y, price y * oddRow M tag ω u y = 0 := by simp [oddRow, hodd]
      rw [hzero]
      exact mul_nonneg (by norm_num) havg
  rw [← expect_weighted_sum P price (fun y ω => oddRow M tag ω u y)]
  change P.expect (fun ω => ∑ y, price y * oddRow M tag ω u y) ≤ 2 * avg
  calc
    P.expect (fun ω => ∑ y, price y * oddRow M tag ω u y) ≤
        P.expect (fun _ => 2 * avg) := by
          unfold FinProb.expect
          apply Finset.sum_le_sum
          intro ω hω
          by_cases hzero : P.w ω = 0
          · simp [hzero]
          · exact mul_le_mul_of_nonneg_left (hpoint ω hzero) (P.nonneg ω)
    _ = 2 * avg := FinProb.expect_const P _

theorem even_price_pure_le {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι) (c₃ : ℝ)
    (hselect : SelectBound M tag c₃) (hfacts : EvenRowFacts M tag)
    (xm : XMasks M tag) (ym : YMasks M tag)
    (ck : Loc β γ n × Key β γ n) (a : EvenRole n)
    (hkey : key β γ n a.1 = ck.2)
    (hnear : _root_.hammingDist ck.1.1 a.1 ≤ radius β γ n)
    (price : Fin N → ℝ) (hprice : ∀ x, 0 ≤ price x)
    (hlow : ∀ x ∈ (xm ck).1,
      price x ≤ 2 * ∑ z, (M.μ (tag ck.2)).w z * price z) :
    ∑ x, price x *
        (prepLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)).expect
          (fun ω => if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) ≤
      2 * (∑ z, (M.μ (tag ck.2)).w z * price z) * wc β γ n c₃ ck.1 := by
  classical
  let P := prepLaw M tag (pointXProf M tag xm) (pointYProf M tag ym)
  let avg := ∑ z, (M.μ (tag ck.2)).w z * price z
  have havg : 0 ≤ avg := by
    dsimp [avg]
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg ((M.μ (tag ck.2)).nonneg z) (hprice z)
  have hrowNonneg (ω : Prep M tag) (f : OddRole n → Fin N) (x : Fin N) :
      0 ≤ evenRowAt M tag ω a (nbrLabels f a) x :=
    (hfacts ω a (nbrLabels f a)).1 x
  have hrowInfo (ω : Prep M tag) (hω : P.w ω ≠ 0)
      (f : OddRole n → Fin N) (x : Fin N)
      (hsel : sel M tag ω a.1 = some ck.1)
      (hx : evenRowAt M tag ω a (nbrLabels f a) x ≠ 0) :
      x ∈ (xm ck).1 ∧ EvLocal M tag ω a ck.1 := by
    have hprofiles := prepLaw_point_masks M tag xm ym ω hω
    rcases (hfacts ω a (nbrLabels f a)).2.2.2.1 x hx with ⟨_, hexists⟩
    rcases hexists with ⟨c', hcsel, hev, hxmask⟩
    have hc : c' = ck.1 := Option.some.inj (hcsel.symm.trans hsel)
    subst c'
    rw [hkey, hprofiles.1] at hxmask
    exact ⟨hxmask, hev⟩
  have hrowPrice (ω : Prep M tag) (hω : P.w ω ≠ 0)
      (f : OddRole n → Fin N) (hsel : sel M tag ω a.1 = some ck.1) :
      ∑ x, price x * evenRowAt M tag ω a (nbrLabels f a) x ≤
        2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0 := by
    by_cases hev : EvLocal M tag ω a ck.1
    · have hreplace :
          (∑ x, price x * evenRowAt M tag ω a (nbrLabels f a) x) =
            ∑ x, if x ∈ (xm ck).1 then
              price x * evenRowAt M tag ω a (nbrLabels f a) x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxmask : x ∈ (xm ck).1
        · simp [hxmask]
        · have hzero : evenRowAt M tag ω a (nbrLabels f a) x = 0 := by
            by_contra hne
            exact hxmask (hrowInfo ω hω f x hsel hne).1
          simp [hxmask, hzero]
      have hsum := (hfacts ω a (nbrLabels f a)).2.1
      rw [hreplace]
      calc
        (∑ x, if x ∈ (xm ck).1 then
            price x * evenRowAt M tag ω a (nbrLabels f a) x else 0) ≤
            ∑ x, 2 * avg * evenRowAt M tag ω a (nbrLabels f a) x := by
              apply Finset.sum_le_sum
              intro x hx
              by_cases hxmask : x ∈ (xm ck).1
              · simp only [if_pos hxmask]
                simpa [avg] using mul_le_mul_of_nonneg_right (hlow x hxmask)
                  (hrowNonneg ω f x)
              · have hzero : evenRowAt M tag ω a (nbrLabels f a) x = 0 := by
                  by_contra hne
                  exact hxmask (hrowInfo ω hω f x hsel hne).1
                simp [hxmask, hzero]
        _ = 2 * avg * ∑ x, evenRowAt M tag ω a (nbrLabels f a) x := by
              rw [← Finset.mul_sum]
        _ ≤ 2 * avg := by
              have hcoeff : 0 ≤ 2 * avg := mul_nonneg (by norm_num) havg
              calc
                2 * avg * ∑ x, evenRowAt M tag ω a (nbrLabels f a) x ≤ 2 * avg * 1 :=
                  mul_le_mul_of_nonneg_left hsum hcoeff
                _ = 2 * avg := by ring
        _ = 2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0 := by simp [hev]
    · have hzero : ∀ x, evenRowAt M tag ω a (nbrLabels f a) x = 0 := by
        intro x
        by_contra hne
        exact hev (hrowInfo ω hω f x hsel hne).2
      simp [hzero, hev]
  have hmeanPrice (ω : Prep M tag) (hω : P.w ω ≠ 0)
      (hsel : sel M tag ω a.1 = some ck.1) :
      ∑ x, price x * evenMean M tag ω a x ≤
        2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0 := by
    let Q := oddDrawLaw M tag ω
    calc
      (∑ x, price x * evenMean M tag ω a x) =
          Q.expect (fun f => ∑ x, price x * evenRowAt M tag ω a (nbrLabels f a) x) := by
            symm
            exact expect_weighted_sum Q price (fun x f =>
              evenRowAt M tag ω a (nbrLabels f a) x)
      _ ≤ Q.expect (fun _ =>
          2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0) :=
            FinProb.expect_mono Q (fun f => hrowPrice ω hω f hsel)
      _ = 2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0 :=
            FinProb.expect_const Q _
  have hprepInner (ω : Prep M tag) (hω : P.w ω ≠ 0) :
      ∑ x, price x *
        (if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0) ≤
          2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0 := by
    by_cases hsel : sel M tag ω a.1 = some ck.1
    · simpa [hsel] using hmeanPrice ω hω hsel
    · have hnot : ¬ EvLocal M tag ω a ck.1 := by
        intro hev
        exact hsel hev.sel_eq
      simp [hsel, hnot]
  have hweighted :
      (∑ x, price x * P.expect (fun ω =>
        if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)) =
        P.expect (fun ω => ∑ x, price x *
          (if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)) :=
    (expect_weighted_sum P price (fun x ω =>
      if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)).symm
  rw [hweighted]
  calc
    P.expect (fun ω => ∑ x, price x *
        (if sel M tag ω a.1 = some ck.1 then evenMean M tag ω a x else 0)) ≤
        P.expect (fun ω => 2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0) := by
          unfold FinProb.expect
          apply Finset.sum_le_sum
          intro ω hω
          by_cases hzero : P.w ω = 0
          · simp [hzero]
          · exact mul_le_mul_of_nonneg_left (hprepInner ω hzero) (P.nonneg ω)
    _ = 2 * avg * P.pr (fun ω => EvLocal M tag ω a ck.1) := by
          calc
            P.expect (fun ω => 2 * avg * if EvLocal M tag ω a ck.1 then 1 else 0) =
                2 * avg * P.expect (fun ω => if EvLocal M tag ω a ck.1 then 1 else 0) :=
                  FinProb.expect_smul P (2 * avg) _
            _ = 2 * avg * P.pr (fun ω => EvLocal M tag ω a ck.1) := by
                  congr 1
                  unfold FinProb.expect FinProb.pr
                  apply Finset.sum_congr rfl
                  intro ω hω
                  by_cases hev : EvLocal M tag ω a ck.1 <;> simp [hev]
    _ ≤ 2 * avg * wc β γ n c₃ ck.1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) havg)
          simpa [P] using hselect (pointXProf M tag xm) (pointYProf M tag ym) a ck.1

theorem pi_profile_mask_expect {β γ : ℝ} {G : Colour} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)}
    (M : Menu4 β γ G n N E X Y) (tag : Key β γ n → M.ι)
    (Q : ∀ j : ProfilePlayers β γ n,
      FinProb (ProfileActions M tag j))
    (g : XMasks M tag × YMasks M tag → ℝ) :
    (FinProb.pi Q).expect (fun σ =>
      g ((profileSumEquiv (A := fun j => ProfileActions M tag j)) σ)) =
      (maskProfileLaw M tag (fun ck => Q (.inl ck)) (fun u => Q (.inr u))).expect g := by
  classical
  let e := profileSumEquiv (A := fun j => ProfileActions M tag j)
  let q : XProf M tag := fun ck => Q (.inl ck)
  let q' : YProf M tag := fun u => Q (.inr u)
  change (FinProb.pi Q).expect (fun σ =>
      g (e σ)) = ((FinProb.pi q).prod (FinProb.pi q')).expect g
  simp only [FinProb.expect, FinProb.pi, FinProb.prod]
  rw [← Equiv.sum_comp e.symm
    (fun σ => (∏ j, (Q j).w (σ j)) * g (e σ))]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xm hxm
  apply Finset.sum_congr rfl
  intro ym hym
  simp only [e, profileSumEquiv]
  rw [Fintype.prod_sum_type]
  simp [q, q']

end HypercubeRamsey.Lane_q_s04_prof
