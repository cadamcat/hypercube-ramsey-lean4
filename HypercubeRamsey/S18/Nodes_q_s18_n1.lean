import HypercubeRamsey.S18.Defs
import HypercubeRamsey.Framework.Minimax
import HypercubeRamsey.Tools.Concentration

namespace HypercubeRamsey.Lane_q_s18_n1

open scoped BigOperators
open HypercubeRamsey.S18

private theorem finProb_pr_mono {A : Type*} [Fintype A] (P : FinProb A)
    {E F : A → Prop} (hEF : ∀ a, E a → F a) : P.pr E ≤ P.pr F := by
  classical
  unfold FinProb.pr
  apply Finset.sum_le_sum
  intro a ha
  by_cases hE : E a
  · have hF : F a := hEF a hE
    simp [hE, hF]
  · by_cases hF : F a
    · simp [hE, hF, P.nonneg a]
    · simp [hE, hF]

private theorem bounded_difference_upper_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (P : ∀ i, FinProb (Ω i)) (f : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hlip : ∀ i (ω ω' : ∀ j, Ω j), (∀ j, j ≠ i → ω j = ω' j) →
      |f ω - f ω'| ≤ c i)
    (hwidth : 0 < ∑ i, c i ^ 2) (δ : ℝ) (hδ : 0 < δ)
    (hmean : (FinProb.pi P).expect f ≤ δ) :
    (FinProb.pi P).pr (fun ω => 2 * δ ≤ f ω) ≤
      2 * Real.exp (-2 * δ ^ 2 / ∑ i, c i ^ 2) := by
  have hsub (ω : ∀ i, Ω i) (hω : 2 * δ ≤ f ω) :
      δ ≤ |f ω - (FinProb.pi P).expect f| := by
    have hgap : δ ≤ f ω - (FinProb.pi P).expect f := by linarith
    exact hgap.trans (le_abs_self _)
  exact (finProb_pr_mono (FinProb.pi P) hsub).trans
    (HypercubeRamsey.xMcDiarmid P f c hc hlip hwidth δ hδ)

private theorem law_eq_of_weights {N : ℕ} {μ ν : Law N}
    (h : ∀ x, μ.w x = ν.w x) : μ = ν := by
  cases μ
  cases ν
  congr 1
  exact funext h

private theorem finLaw_eq_of_weights {A : Type*} [Fintype A] {P Q : FinLaw A}
    (h : ∀ x, P.w x = Q.w x) : P = Q := by
  cases P
  cases Q
  congr 1
  exact funext h

private theorem normalize_indicator_eq_cond {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : HypercubeRamsey.S18.LateData hPT)
    (μ : Law (T.S.N k)) (A : Finset (Fin (T.S.N k)))
    (hA : 0 < ∑ x ∈ A, μ.w x) :
    D.normalize (fun x => μ.w x * (if x ∈ A then (1 : ℝ) else 0)) = μ.cond A hA := by
  classical
  have hmass : (∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0)) =
      ∑ x ∈ A, μ.w x := by
    simp [Finset.sum_ite_mem]
  have hnonneg : ∀ x, 0 ≤ μ.w x * (if x ∈ A then (1 : ℝ) else 0) := by
    intro x
    split_ifs with hx
    · exact mul_nonneg (μ.nonneg x) (by norm_num)
    · simp
  have hpos : 0 < ∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0) := by
    rw [hmass]
    exact hA
  have hbranch :
      (∀ x, 0 ≤ μ.w x * (if x ∈ A then (1 : ℝ) else 0)) ∧
        0 < ∑ x, μ.w x * (if x ∈ A then (1 : ℝ) else 0) := ⟨hnonneg, hpos⟩
  apply law_eq_of_weights
  intro x
  simp only [HypercubeRamsey.S18.LateData.normalize, dif_pos hbranch]
  simp only [Law.cond, Law.restrict]
  by_cases hx : x ∈ A <;> simp [hx]

private theorem law_cond_atom_cap {N : ℕ} (μ : Law N) (A : Finset (Fin N))
    (hA : 0 < ∑ x ∈ A, μ.w x) (M : ℝ) (hM : 0 ≤ M)
    (hcap : ∀ x, μ.w x ≤ M) :
    ∀ x, (μ.cond A hA).w x ≤ M / (∑ y ∈ A, μ.w y) := by
  intro x
  change (if x ∈ A then μ.w x / (∑ y ∈ A, μ.w y) else 0) ≤
    M / (∑ y ∈ A, μ.w y)
  split_ifs with hx
  · exact (div_le_div_iff_of_pos_right hA).2 (hcap x)
  · exact div_nonneg hM hA.le

private theorem uniformWeight_total {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty) :
    (∑ y, if y ∈ S then (1 / (S.card : ℝ)) else 0) = 1 := by
  classical
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hS).ne'
  field_simp

private theorem weighted_sub_sum {A : Type*} [Fintype A]
    (w : A → ℝ) (hw : (∑ a, w a) = 1) (g : A → ℝ) (c : ℝ) :
    (∑ a, w a * (g a - c)) = (∑ a, w a * g a) - c := by
  calc
    (∑ a, w a * (g a - c)) = ∑ a, (w a * g a - w a * c) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a, w a * g a) - (∑ a, w a * c) := by rw [Finset.sum_sub_distrib]
    _ = (∑ a, w a * g a) - c := by rw [← Finset.sum_mul, hw]; ring

private theorem exists_balanced_mixture {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (v : A → B → ℝ) (cap : ℝ)
    (hprice : ∀ q : FinLaw B, ∃ a,
      (∑ b, q.w b * v a b) ≤ cap) :
    ∃ p : FinLaw A, ∀ b, (∑ a, p.w a * v a b) ≤ cap := by
  have hpriceProb : ∀ q : FinProb B, ∃ a,
      (∑ b, q.w b * (v a b - cap)) ≤ 0 := by
    intro q
    let qLaw : FinLaw B := ⟨q.w, q.nonneg, q.sum_eq_one⟩
    obtain ⟨a, ha⟩ := hprice qLaw
    refine ⟨a, ?_⟩
    rw [weighted_sub_sum q.w q.sum_eq_one (fun b => v a b) cap]
    linarith
  obtain ⟨p, hp⟩ := finite_minimax (fun a b => v a b - cap) hpriceProb
  let pLaw : FinLaw A := ⟨p.w, p.nonneg, p.sum_eq_one⟩
  refine ⟨pLaw, ?_⟩
  intro b
  have hb : (∑ a, pLaw.w a * (v a b - cap)) ≤ 0 := by
    simpa [pLaw] using hp b
  have heq := weighted_sub_sum pLaw.w pLaw.sum_one (fun a => v a b) cap
  rw [heq] at hb
  linarith

private theorem exists_cheap_half {B : Type*} [Fintype B] [DecidableEq B]
    [Nonempty B] (q : FinLaw B) :
    ∃ S : Finset B, (Fintype.card B : ℝ) ≤ 2 * (S.card : ℝ) ∧
      ∀ y ∈ S, q.w y ≤ 2 / (Fintype.card B : ℝ) := by
  classical
  let cutoff : ℝ := 2 / (Fintype.card B : ℝ)
  let cheap : Finset B := Finset.univ.filter fun y => q.w y ≤ cutoff
  let costly : Finset B := Finset.univ.filter fun y => cutoff < q.w y
  have hcardpos : 0 < (Fintype.card B : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcardEqNat : cheap.card + costly.card = Fintype.card B := by
    dsimp [cheap, costly]
    simpa [cutoff, not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset B))
        (p := fun y => q.w y ≤ cutoff))
  have hcardEq : (cheap.card : ℝ) + (costly.card : ℝ) =
      (Fintype.card B : ℝ) := by exact_mod_cast hcardEqNat
  have hcostlyMass : (∑ y ∈ costly, q.w y) ≤ 1 := by
    calc
      (∑ y ∈ costly, q.w y) =
          ∑ y, if y ∈ costly then q.w y else 0 := by
            simp [Finset.sum_ite_mem]
      _ ≤ ∑ y, q.w y := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases h : y ∈ costly
        · simp [h]
        · simp [h, q.nonneg y]
      _ = 1 := q.sum_one
  have hcheapBound : (Fintype.card B : ℝ) ≤ 2 * (cheap.card : ℝ) := by
    by_contra hnot
    have hsmallCheap : 2 * cheap.card < Fintype.card B := by
      exact_mod_cast (lt_of_not_ge hnot)
    have hrealSmallCheap : 2 * (cheap.card : ℝ) < (Fintype.card B : ℝ) := by
      exact_mod_cast hsmallCheap
    have hlargeCostly : (Fintype.card B : ℝ) < 2 * (costly.card : ℝ) := by
      nlinarith [hcardEq]
    have hcostlyPos : 0 < costly.card := by
      have : (0 : ℝ) < (costly.card : ℝ) := by nlinarith [hlargeCostly]
      exact_mod_cast this
    have hstrict : (costly.card : ℝ) * cutoff <
        ∑ y ∈ costly, q.w y := by
      have hsumConst : (costly.card : ℝ) * cutoff = ∑ y ∈ costly, cutoff := by
        simp [Finset.sum_const, nsmul_eq_mul]
      obtain ⟨y, hy⟩ := Finset.card_pos.mp hcostlyPos
      have hylt : cutoff < q.w y := by
        simpa [costly] using hy
      rw [hsumConst]
      apply Finset.sum_lt_sum
      · intro z hz
        have hzlt : cutoff < q.w z := by simpa [costly] using hz
        exact le_of_lt hzlt
      · exact ⟨y, hy, hylt⟩
    have hscaled : (2 * (costly.card : ℝ)) / (Fintype.card B : ℝ) < 1 := by
      calc
        (2 * (costly.card : ℝ)) / (Fintype.card B : ℝ) =
            (costly.card : ℝ) * cutoff := by dsimp [cutoff]; ring
        _ < ∑ y ∈ costly, q.w y := hstrict
        _ ≤ 1 := hcostlyMass
    have hcostlySmall : 2 * (costly.card : ℝ) < (Fintype.card B : ℝ) := by
      have hh := (div_lt_iff₀ hcardpos).mp hscaled
      nlinarith [hh]
    nlinarith [hcardEq, hrealSmallCheap, hcostlySmall]
  refine ⟨cheap, hcheapBound, ?_⟩
  intro y hy
  simpa [cheap, cutoff] using hy

private theorem price_expectation_le_of_support {B : Type*} [Fintype B]
    (P : FinLaw B) (support : Finset B) (price : B → ℝ) (cap : ℝ)
    (hsupp : ∀ y, P.w y ≠ 0 → y ∈ support)
    (hprice : ∀ y ∈ support, price y ≤ cap) :
    (∑ y, price y * P.w y) ≤ cap := by
  calc
    (∑ y, price y * P.w y) ≤ ∑ y, P.w y * cap := by
      apply Finset.sum_le_sum
      intro y hy
      by_cases hzero : P.w y = 0
      · simp [hzero]
      · have hpos : 0 < P.w y := lt_of_le_of_ne (P.nonneg y) (Ne.symm hzero)
        have hyprice : price y ≤ cap := hprice y (hsupp y hzero)
        calc
          price y * P.w y ≤ cap * P.w y := mul_le_mul_of_nonneg_right hyprice (P.nonneg y)
          _ = P.w y * cap := by ring
    _ = cap := by rw [← Finset.sum_mul, P.sum_one]; ring

private theorem exists_balanced_history_mixture {H M Y : Type*}
    [Fintype H] [Fintype M] [Fintype Y] [Nonempty M] [Nonempty Y]
    (history : FinLaw H) (maskLabels : M → Finset Y)
    (labelLaw : H → M → FinLaw Y) (cap : ℝ)
    (hsupport : ∀ h m y, (labelLaw h m).w y ≠ 0 → y ∈ maskLabels m)
    (hcheap : ∀ q : FinLaw Y, ∃ m, ∀ y ∈ maskLabels m, q.w y ≤ cap) :
    ∃ mix : FinLaw M, ∀ y,
      (∑ m, mix.w m * (∑ h, history.w h * (labelLaw h m).w y)) ≤ cap := by
  apply exists_balanced_mixture
  intro q
  obtain ⟨m, hm⟩ := hcheap q
  refine ⟨m, ?_⟩
  have hinner (h : H) :
      (∑ y, q.w y * (labelLaw h m).w y) ≤ cap :=
    price_expectation_le_of_support (labelLaw h m) (maskLabels m) q.w cap
      (hsupport h m) hm
  calc
    (∑ y, q.w y * (∑ h, history.w h * (labelLaw h m).w y)) =
        ∑ h, history.w h * (∑ y, q.w y * (labelLaw h m).w y) := by
      calc
        _ = ∑ y, ∑ h, history.w h * (q.w y * (labelLaw h m).w y) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h hh
          ring
        _ = ∑ h, ∑ y, history.w h * (q.w y * (labelLaw h m).w y) := by
          rw [Finset.sum_comm]
        _ = ∑ h, history.w h * (∑ y, q.w y * (labelLaw h m).w y) := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [Finset.mul_sum]
    _ ≤ ∑ h, history.w h * cap := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left (hinner h) (history.nonneg h)
    _ = cap := by rw [← Finset.sum_mul, history.sum_one]; ring

private theorem labelWeight_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
    0 ≤ D.labelWeight j side tests y := by
  unfold LateData.labelWeight
  split_ifs with hmass hpass
  · apply div_nonneg
    · unfold LateData.maskWeight
      split_ifs <;> positivity
    · exact (Real.exp_pos _).le.trans hmass
  · simp
  · unfold LateData.maskWeight
    split_ifs <;> positivity

private theorem labelWeight_total {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmask : side.1.1.Nonempty) :
    (∑ y, D.labelWeight j side tests y) = 1 := by
  classical
  unfold LateData.labelWeight
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side tests
  · simp_rw [if_pos hmass]
    have hden : 0 < D.retainedMass j side tests :=
      (Real.exp_pos _).trans_le hmass
    calc
      (∑ y, if D.passes j side tests y then
          D.maskWeight side y / D.retainedMass j side tests else 0) =
          (∑ y, if D.passes j side tests y then D.maskWeight side y else 0) /
            D.retainedMass j side tests := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro y hy
              split_ifs <;> simp
      _ = D.retainedMass j side tests / D.retainedMass j side tests := by
        simp [LateData.retainedMass]
      _ = 1 := div_self (ne_of_gt hden)
  · simp_rw [if_neg hmass]
    have hmasktotal := uniformWeight_total side.1.1 hmask
    simpa [LateData.maskWeight] using hmasktotal

private theorem labelWeight_zero_of_not_mask {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k))
    (hy : y ∉ side.1.1) : D.labelWeight j side tests y = 0 := by
  by_cases hmass : Real.exp (-(κ.α / 100) * (T.S.n k : ℝ)) ≤
      D.retainedMass j side tests
  · simp [LateData.labelWeight, hmass, LateData.maskWeight, hy]
  · simp [LateData.labelWeight, hmass, LateData.maskWeight, hy]

private noncomputable def lateLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} (side : D.encoding.base.RowOut b)
    (tests : Finset (Fin (T.S.n k))) (hmask : side.1.1.Nonempty) :
    FinLaw {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} where
  w y := D.labelWeight j side tests y.1
  nonneg y := labelWeight_nonneg D j side tests y.1
  sum_one := by
    classical
    let pool := D.encoding.base.latePoolOf b
    have hzero (y : Fin (T.S.N k)) (hy : y ∉ pool) :
        D.labelWeight j side tests y = 0 := by
      apply labelWeight_zero_of_not_mask D j side tests y
      intro hmem
      exact hy (side.1.2.1 hmem)
    have hsubtype :
        (∑ y : {y : Fin (T.S.N k) // y ∈ pool}, D.labelWeight j side tests y.1) =
          ∑ y ∈ pool, D.labelWeight j side tests y := by
      simpa [pool] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (Fin (T.S.N k))))
          (p := fun y => y ∈ pool) (f := fun y => D.labelWeight j side tests y))
    have hpoolSum : (∑ y ∈ pool, D.labelWeight j side tests y) =
        ∑ y, D.labelWeight j side tests y := by
      have hcomp : (∑ y ∈ Finset.univ \ pool, D.labelWeight j side tests y) = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        exact hzero y (Finset.mem_sdiff.mp hy).2
      calc
        (∑ y ∈ pool, D.labelWeight j side tests y) =
            (∑ y ∈ pool, D.labelWeight j side tests y) + 0 := by ring
        _ = ∑ y, D.labelWeight j side tests y := by
          rw [← Finset.sum_sdiff pool.subset_univ, hcomp]
          ring
    rw [hsubtype, hpoolSum]
    exact labelWeight_total D j side tests hmask

private theorem allowedMask_nonempty {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (mask : D.encoding.base.AllowedMask b) : mask.1.Nonempty := by
  have hclass : D.geom.classOf b = some j := (D.encoding.base.class_of_spec b j).1 hb
  have hpoolpos : 0 < (D.encoding.base.latePoolOf b).card := by
    simpa [LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
  have hmaskpos : 0 < mask.1.card := by omega
  exact Finset.card_pos.mp hmaskpos

private noncomputable def rowSide {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (mask : D.encoding.base.AllowedMask b)
    (sketch : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :
    D.encoding.base.RowOut b := by
  let hclass : D.geom.classOf b = some j := (D.encoding.base.class_of_spec b j).1 hb
  have hpoolpos : 0 < (D.encoding.base.latePoolOf b).card := by
    simpa [LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
  have hpool : Nonempty {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} := by
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpoolpos
    exact ⟨⟨y, hy⟩⟩
  let y₀ : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} := Classical.choice hpool
  exact ⟨mask, (sketch, y₀)⟩

private noncomputable def asFinLaw {N : ℕ} (P : Law N) : FinLaw (Fin N) :=
  ⟨P.w, P.nonneg, P.sum_eq_one⟩

private noncomputable def rowSketchLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k)
    (h : D.encoding.base.History j.castSucc) :
    FinLaw (Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :=
  FinLaw.pi (fun a : Fin (T.S.n k) =>
    FinLaw.pi (fun t : Fin (sketchLength T k) =>
      asFinLaw (D.currentPrior j (flipPos b a) h)))

private noncomputable def rowSketchLabelJoint {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (history : FinLaw (D.encoding.base.History j.castSucc))
    (mask : D.encoding.base.AllowedMask b) :
    FinLaw (D.encoding.base.History j.castSucc ×
      ((Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) ×
        {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b})) :=
  FinLaw.bind history (fun h =>
    FinLaw.bind (rowSketchLaw D j b h) (fun sketch =>
      lateLabelLaw D j (rowSide D j b hb mask sketch) Finset.univ
        (allowedMask_nonempty D j b hb mask)))

private noncomputable def rowFixedMaskLabelLaw {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (history : FinLaw (D.encoding.base.History j.castSucc))
    (mask : D.encoding.base.AllowedMask b) :
    FinLaw {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} :=
  FinLaw.map (rowSketchLabelJoint D j b hb history mask) (fun z => z.2.2)

private noncomputable def rowMaskLabels {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    {b : Pos T k} (mask : D.encoding.base.AllowedMask b) :
    Finset {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b} :=
  Finset.univ.filter fun y => y.1 ∈ mask.1

private theorem rowFixedMaskLabelLaw_supported {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (history : FinLaw (D.encoding.base.History j.castSucc))
    (mask : D.encoding.base.AllowedMask b) (y : {y : Fin (T.S.N k) //
      y ∈ D.encoding.base.latePoolOf b})
    (hy : y ∉ rowMaskLabels D mask) :
    (rowFixedMaskLabelLaw D j b hb history mask).w y = 0 := by
  classical
  have hnot : y.1 ∉ mask.1 := by simpa [rowMaskLabels] using hy
  unfold rowFixedMaskLabelLaw rowSketchLabelJoint
  simp only [FinLaw.map, FinLaw.bind]
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hzy : z.2.2 = y
  · subst y
    cases z with
    | mk h rest =>
      cases rest with
      | mk sketch label =>
        have hnotSide : label.1 ∉ (rowSide D j b hb mask sketch).1.1 := by
          simpa [rowSide] using hnot
        have hweight := labelWeight_zero_of_not_mask D j
          (rowSide D j b hb mask sketch) Finset.univ label.1 hnotSide
        simp [lateLabelLaw, hweight]
  · simp [hzy]

private theorem exists_row_mask_profile {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (history : FinLaw (D.encoding.base.History j.castSucc)) (cap : ℝ)
    (hprice : ∀ q : FinLaw {y : Fin (T.S.N k) //
        y ∈ D.encoding.base.latePoolOf b},
      ∃ mask : D.encoding.base.AllowedMask b,
        ∀ y ∈ rowMaskLabels D mask, q.w y ≤ cap) :
    ∃ mix : FinLaw (D.encoding.base.AllowedMask b), ∀ y,
      (∑ mask, mix.w mask * (rowFixedMaskLabelLaw D j b hb history mask).w y) ≤ cap := by
  have hmask : Nonempty (D.encoding.base.AllowedMask b) := by
    refine ⟨⟨D.encoding.base.latePoolOf b, Finset.Subset.rfl, ?_⟩⟩
    omega
  have hlabel : Nonempty {y : Fin (T.S.N k) //
      y ∈ D.encoding.base.latePoolOf b} := by
    have hclass := (D.encoding.base.class_of_spec b j).1 hb
    have hpoolpos : 0 < (D.encoding.base.latePoolOf b).card := by
      simpa [LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpoolpos
    exact ⟨⟨y, hy⟩⟩
  apply exists_balanced_mixture
  intro q
  obtain ⟨mask, hm⟩ := hprice q
  refine ⟨mask, ?_⟩
  have hsupp (y : {y : Fin (T.S.N k) //
      y ∈ D.encoding.base.latePoolOf b}) :
      (rowFixedMaskLabelLaw D j b hb history mask).w y ≠ 0 →
        y ∈ rowMaskLabels D mask := by
    intro hy
    by_contra hnot
    exact hy (rowFixedMaskLabelLaw_supported D j b hb history mask y hnot)
  exact price_expectation_le_of_support (rowFixedMaskLabelLaw D j b hb history mask)
    (rowMaskLabels D mask) q.w cap hsupp hm

private theorem rowMask_price_response {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (q : FinLaw {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) :
    ∃ mask : D.encoding.base.AllowedMask b,
      ∀ y ∈ rowMaskLabels D mask, q.w y ≤ 2 / ((D.encoding.base.latePoolOf b).card : ℝ) := by
  classical
  let pool := D.encoding.base.latePoolOf b
  let Label := {y : Fin (T.S.N k) // y ∈ pool}
  have hclass := (D.encoding.base.class_of_spec b j).1 hb
  have hpoolpos : 0 < pool.card := by
    simpa [pool, LateProcessBase.latePoolOf, hclass] using D.late_pool_pos j
  have hlabel : Nonempty Label := by
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpoolpos
    exact ⟨⟨y, hy⟩⟩
  letI : Nonempty Label := hlabel
  have hcardLabel : Fintype.card Label = pool.card := Fintype.card_coe pool
  obtain ⟨cheap, hcheapCard, hcheapPrice⟩ := exists_cheap_half q
  let S : Finset (Fin (T.S.N k)) := cheap.image Subtype.val
  have hSsub : S ⊆ pool := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact z.2
  have hScard : S.card = cheap.card := by
    simpa [S] using Finset.card_image_of_injective cheap Subtype.val_injective
  have hcheapCardNat : Fintype.card Label ≤ 2 * cheap.card := by
    exact_mod_cast hcheapCard
  have hSlarge : pool.card ≤ 2 * S.card := by
    calc
      pool.card = Fintype.card Label := hcardLabel.symm
      _ ≤ 2 * cheap.card := hcheapCardNat
      _ = 2 * S.card := by rw [hScard]
  let mask : D.encoding.base.AllowedMask b := ⟨S, hSsub, hSlarge⟩
  have hlabels : rowMaskLabels D mask = cheap := by
    ext y
    simp only [rowMaskLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    change y.1 ∈ S ↔ y ∈ cheap
    change y.1 ∈ cheap.image Subtype.val ↔ y ∈ cheap
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, hzy⟩
      have hzEq : z = y := Subtype.ext hzy
      simpa [hzEq] using hz
    · intro hy
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  refine ⟨mask, ?_⟩
  intro y hy
  have hycheap : y ∈ cheap := hlabels ▸ hy
  simpa [hcardLabel, pool] using hcheapPrice y hycheap

private theorem exists_row_balanced_profile {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (history : FinLaw (D.encoding.base.History j.castSucc)) :
    ∃ mix : FinLaw (D.encoding.base.AllowedMask b), ∀ y,
      (∑ mask, mix.w mask * (rowFixedMaskLabelLaw D j b hb history mask).w y) ≤
        2 / ((D.encoding.base.latePoolOf b).card : ℝ) := by
  exact exists_row_mask_profile D j b hb history
    (2 / ((D.encoding.base.latePoolOf b).card : ℝ))
    (fun q => rowMask_price_response D j b hb q)

private noncomputable def explicitRowKernel {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (h : D.encoding.base.History j.castSucc)
    (maskProfile : FinLaw (D.encoding.base.AllowedMask b)) :
    FinLaw (D.encoding.base.RowOut b) :=
  FinLaw.bind maskProfile (fun mask =>
    FinLaw.bind (rowSketchLaw D j b h) (fun sketch =>
      lateLabelLaw D j (rowSide D j b hb mask sketch) Finset.univ
        (allowedMask_nonempty D j b hb mask)))

private theorem finLaw_map_bind_fst {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A]
    (P : FinLaw A) (K : A → FinLaw C) :
    FinLaw.map (FinLaw.bind P K) Prod.fst = P := by
  apply finLaw_eq_of_weights
  intro a
  simp only [FinLaw.map, FinLaw.bind]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x, ∑ y, if x = a then P.w x * (K x).w y else 0) =
        ∑ x, if x = a then P.w x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxa : x = a
      · subst x
        simp only [if_pos rfl, if_true]
        rw [← Finset.mul_sum, (K a).sum_one, mul_one]
      · simp [hxa]
    _ = P.w a := by simp

private theorem labelWeight_side_congr {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) {b : Pos T k} {side₁ side₂ : D.encoding.base.RowOut b}
    (hm : side₁.1 = side₂.1) (hs : side₁.2.1 = side₂.2.1)
    (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
    D.labelWeight j side₁ tests y = D.labelWeight j side₂ tests y := by
  cases side₁ with
  | mk m₁ r₁ =>
    cases r₁ with
    | mk s₁ y₁ =>
      cases side₂ with
      | mk m₂ r₂ =>
        cases r₂ with
        | mk s₂ y₂ =>
          dsimp at hm hs
          subst m₂
          subst s₂
          rfl

private theorem explicitRowKernel_formula {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (h : D.encoding.base.History j.castSucc)
    (maskProfile : FinLaw (D.encoding.base.AllowedMask b))
    (out : D.encoding.base.RowOut b) :
    (explicitRowKernel D j b hb h maskProfile).w out =
      maskProfile.w out.1 *
    (∏ a, ∏ t, (D.currentPrior j (flipPos b a) h).w (out.2.1 a t)) *
    D.labelWeight j out Finset.univ out.2.2.1 := by
  simp only [explicitRowKernel, FinLaw.bind, rowSketchLaw, FinLaw.pi, lateLabelLaw,
    asFinLaw]
  have hweight := labelWeight_side_congr (D := D) (j := j)
    (side₁ := rowSide D j b hb out.1 out.2.1) (side₂ := out)
    (by rfl) (by rfl) Finset.univ out.2.2.1
  rw [hweight]
  ring

private theorem explicitRowKernel_mask_marginal {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (j : Fin D.geom.r) (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (h : D.encoding.base.History j.castSucc)
    (maskProfile : FinLaw (D.encoding.base.AllowedMask b)) :
    FinLaw.map (explicitRowKernel D j b hb h maskProfile)
      (fun out : D.encoding.base.RowOut b => out.1) = maskProfile := by
  let K : D.encoding.base.AllowedMask b →
      FinLaw ((Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) ×
        {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) := fun mask =>
    FinLaw.bind (rowSketchLaw D j b h) (fun sketch =>
      lateLabelLaw D j (rowSide D j b hb mask sketch) Finset.univ
        (allowedMask_nonempty D j b hb mask))
  simpa [explicitRowKernel, K] using finLaw_map_bind_fst maskProfile K

private noncomputable def kernelsFromProfiles {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (profiles : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b)) :
    LateKernels D.encoding.base where
  maskProfile := profiles
  refK := fun j b h => explicitRowKernel D j b.1 b.2 h (profiles b.1)
  refK_mask_marginal := fun j b h =>
    explicitRowKernel_mask_marginal D j b.1 b.2 h (profiles b.1)

private theorem transitionData_of_profiles {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (profiles : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b)) :
    TransitionData (D.withKernels (kernelsFromProfiles D profiles)) := by
  refine ⟨?_⟩
  intro j b h out
  exact explicitRowKernel_formula D j b.1 b.2 h (profiles b.1) out

private theorem withKernels_spec {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (hD : D.Spec) (K : LateKernels D.encoding.base) : (D.withKernels K).Spec := by
  rcases hD with ⟨hcorner, hfresh, hthresholds, hcalibration, hbad, hbadPinned,
    htypical, hsingleton, hscope, hcounts, hseparation, hevents, hcap,
    hsuccess, hlocal⟩
  have hperm : D.encoding.permLaw = (D.withKernels K).encoding.permLaw := by rfl
  have hup (f) : D.upstreamBad f = (D.withKernels K).upstreamBad f := by
    cases f <;> rfl
  refine ⟨hcorner, hfresh, hthresholds, hcalibration, ?_, ?_, htypical,
    hsingleton, ?_, hcounts, hseparation, ?_, hcap, ?_, hlocal⟩
  · intro f
    rw [← hperm, ← hup f]
    exact hbad f
  · intro C slot bin f
    rw [← hperm, ← hup f]
    exact hbadPinned C slot bin f
  · intro v
    change D.encoding.events.scope v = D.directCells v
    exact hscope v
  · intro v s
    change D.encoding.events.S v s ↔ IsEvenRole v ∧ D.listFailure v s
    exact hevents v s
  · intro x hx htypical' havoid v hv
    change D.initialValid v (D.encoding.initialState x)
    exact hsuccess x hx htypical' havoid v hv

private theorem lateError_pos {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} (i : Fin PT.tiling.m) (remaining : ℕ) :
    0 < lateError κ T k PT i remaining := by
  have hd : 0 < densityScale T k := by
    unfold densityScale
    exact div_pos (by exact_mod_cast T.S.N_pos k) (by positivity)
  unfold lateError
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hd _) (Real.exp_pos _))
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)

private theorem error_nonneg {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (v : Pos T k) (j : Fin D.geom.r) : 0 ≤ D.error v j := by
  unfold LateData.error
  exact (lateError_pos (κ := κ) (T := T) (k := k) (PT := PT) (D.geom.patchOf v)
    (D.geom.r - j.val)).le

private theorem smallErrors_sum_control {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (v : Pos T k) :
    (∑ j : Fin D.geom.r, D.error v j) ≤ Real.log 2 / 1000 := by
  let i := D.geom.patchOf v
  have hmax : 1 ≤ (max 1 (PT.tiling.P i).h : ℝ) := le_max_left _ _
  have hsum_nonneg : 0 ≤ ∑ j : Fin D.geom.r,
      lateError κ T k PT i (D.geom.r - j.val) :=
    Finset.sum_nonneg fun j hj => by
      exact (lateError_pos (κ := κ) (T := T) (k := k) (PT := PT) i
        (D.geom.r - j.val)).le
  have hbound := hsmall i
  calc
    (∑ j : Fin D.geom.r, D.error v j) =
        ∑ j : Fin D.geom.r, lateError κ T k PT i (D.geom.r - j.val) := by
          simp [LateData.error, i]
    _ ≤ (max 1 (PT.tiling.P i).h : ℝ) *
          (∑ j : Fin D.geom.r, lateError κ T k PT i (D.geom.r - j.val)) := by
      calc
        _ = 1 * (∑ j : Fin D.geom.r,
            lateError κ T k PT i (D.geom.r - j.val)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmax hsum_nonneg
    _ ≤ Real.log 2 / 1000 := hbound

/-- The finite reverse geometric sum is bounded by the infinite geometric sum. -/
theorem finite_reverse_geometric_sum_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (r : ℕ) :
    (∑ j : Fin r, q ^ (r - j.val)) ≤ 1 / (1 - q) := by
  let S : ℕ → ℝ := fun r => ∑ j : Fin r, q ^ (r - j.val)
  have hform : ∀ r, S r * (1 - q) = q - q ^ (r + 1) := by
    intro r
    induction r with
    | zero => simp [S]
    | succ r ih =>
      have hrec : S (r + 1) = q ^ (r + 1) + S r := by
        dsimp [S]
        rw [Fin.sum_univ_succ]
        simp
      rw [hrec]
      calc
        (q ^ (r + 1) + S r) * (1 - q) =
            q ^ (r + 1) * (1 - q) + (q - q ^ (r + 1)) := by rw [add_mul, ih]
        _ = q - q ^ (r + 1) * q := by ring
        _ = q - q ^ (r + 2) := by
          congr 2
  have hden : 0 < 1 - q := by linarith
  have hnum : q - q ^ (r + 1) ≤ 1 := by
    have hp : 0 ≤ q ^ (r + 1) := pow_nonneg hq0.le _
    linarith
  apply (le_div_iff₀ hden).2
  change S r * (1 - q) ≤ 1
  rw [hform r]
  exact hnum

/-- The losses from successive hit conditioning are bounded by twice the
corresponding power of two when their total error is at most `log 2 / 12`. -/
theorem reciprocal_survival_product_le {r : ℕ} (e : Fin r → ℝ)
    (he0 : ∀ i, 0 ≤ e i) (he12 : ∀ i, e i ≤ 1 / 12)
    (hsum : (∑ i, e i) ≤ Real.log 2 / 12) :
    (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤ 2 * (2 : ℝ) ^ r := by
  have hfactor (i : Fin r) : (1 / 2 - 3 * e i)⁻¹ ≤ 2 * Real.exp (12 * e i) := by
    let x : ℝ := 6 * e i
    have hx0 : 0 ≤ x := by dsimp [x]; exact mul_nonneg (by norm_num) (he0 i)
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      nlinarith [he12 i]
    have hden : 0 < 1 - x := by linarith
    have hinv : (1 - x)⁻¹ ≤ 1 + 2 * x := by
      apply (inv_le_iff_one_le_mul₀ hden).2
      nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2 * x by linarith)]
    have hexp : 1 + 2 * x ≤ Real.exp (2 * x) := by
      have := Real.add_one_le_exp (2 * x)
      linarith
    have hrewrite : 1 / 2 - 3 * e i = (1 - x) / 2 := by
      dsimp [x]
      ring
    rw [hrewrite]
    have hInv : ((1 - x) / 2)⁻¹ = 2 * (1 - x)⁻¹ := by
      field_simp [hden.ne']
    rw [hInv]
    have htwox : 2 * x = 12 * e i := by dsimp [x]; ring
    rw [← htwox]
    exact mul_le_mul_of_nonneg_left (le_trans hinv hexp) (by norm_num)
  have hprod : (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤
      ∏ i : Fin r, (2 * Real.exp (12 * e i)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      have hi' := he12 i
      have hpos : 0 < 1 / 2 - 3 * e i := by nlinarith [hi']
      exact inv_nonneg.mpr hpos.le
    · intro i hi
      exact hfactor i
  have hprodEq : (∏ i : Fin r, (2 * Real.exp (12 * e i))) =
      (2 : ℝ) ^ r * Real.exp (12 * ∑ i, e i) := by
    rw [Finset.prod_mul_distrib]
    have hconst : (∏ i : Fin r, (2 : ℝ)) = (2 : ℝ) ^ r := by simp
    rw [hconst]
    congr 1
    have hExp : ∀ s : Finset (Fin r),
        (∏ i ∈ s, Real.exp (12 * e i)) = Real.exp (12 * ∑ i ∈ s, e i) := by
      intro s
      classical
      induction s using Finset.induction with
      | empty => simp
      | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ← Real.exp_add]
          congr 1
          ring
    simpa using hExp Finset.univ
  have hexpsum : Real.exp (12 * ∑ i, e i) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
    calc
      12 * ∑ i, e i ≤ 12 * (Real.log 2 / 12) := by nlinarith
      _ = Real.log 2 := by field_simp
  rw [hprodEq] at hprod
  have hpow : 0 ≤ (2 : ℝ) ^ r := pow_nonneg (by norm_num) _
  calc
    (∏ i, (1 / 2 - 3 * e i)⁻¹) ≤ (2 : ℝ) ^ r * Real.exp (12 * ∑ i, e i) := hprod
    _ ≤ (2 : ℝ) ^ r * 2 := mul_le_mul_of_nonneg_left hexpsum hpow
    _ = 2 * (2 : ℝ) ^ r := by ring

private theorem smallErrors_survival_product_le {κ : CConsts} {T : Stage} {k : ℕ}
    {PT : ProfiledTiling κ T k} {hPT : PT.Valid} (D : LateData hPT)
    (hsmall : SmallErrors κ T k PT D.geom (Real.log 2 / 1000))
    (v : Pos T k) :
    (∏ j : Fin D.geom.r, (1 / 2 - 3 * D.error v j)⁻¹) ≤
      2 * (2 : ℝ) ^ D.geom.r := by
  have hsum := smallErrors_sum_control D hsmall v
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have he12 (j : Fin D.geom.r) : D.error v j ≤ 1 / 12 := by
    have hterm := Finset.single_le_sum
      (fun i hi => error_nonneg D v i) (Finset.mem_univ j)
    calc
      D.error v j ≤ ∑ i : Fin D.geom.r, D.error v i := hterm
      _ ≤ Real.log 2 / 1000 := hsum
      _ ≤ 1 / 12 := by nlinarith [hlog1]
  have hsum' : (∑ j : Fin D.geom.r, D.error v j) ≤ Real.log 2 / 12 := by
    calc
      (∑ j : Fin D.geom.r, D.error v j) ≤ Real.log 2 / 1000 := hsum
      _ ≤ Real.log 2 / 12 := by nlinarith [hlog0]
  exact reciprocal_survival_product_le (e := D.error v)
    (fun j => error_nonneg D v j) he12 hsum'

end HypercubeRamsey.Lane_q_s18_n1

namespace HypercubeRamsey.Lane_sol_s18_n1
set_option backward.isDefEq.respectTransparency false
open Classical
open scoped BigOperators
open S18 Lane_q_s18_n1

private theorem E_map {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinLaw A) (f : A → B) (g : B → ℝ) :
    (FinLaw.map P f).E g = P.E (fun a => g (f a)) := by
  classical
  unfold FinLaw.E FinLaw.map
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp

private theorem E_bind {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (K : A → FinLaw B) (g : A × B → ℝ) :
    (FinLaw.bind P K).E g = P.E (fun a => (K a).E (fun b => g (a,b))) := by
  unfold FinLaw.E FinLaw.bind
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem E_const {A : Type*} [Fintype A] (P : FinLaw A) (c : ℝ) :
    P.E (fun _ => c) = c := by
  simp [FinLaw.E, ← Finset.sum_mul, P.sum_one]

private theorem pr_eq_E {A : Type*} [Fintype A] (P : FinLaw A) (A' : A → Prop) :
    P.pr A' = P.E (fun a => if A' a then 1 else 0) := by
  classical
  unfold FinLaw.pr FinLaw.E
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : A' a <;> simp [h]

private theorem E_pi_eval {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (P : ∀ i, FinLaw (A i))
    (i : I) (g : A i → ℝ) : (FinLaw.pi P).E (fun z => g (z i)) = (P i).E g := by
  let Q : ∀ i, FinProb (A i) := fun i => ⟨(P i).w, (P i).nonneg, (P i).sum_one⟩
  -- Use the singleton marginal via independence of the remaining coordinates.
  have hm := FinProb.pi_marginal_expect Q {i} (fun z => g (z ⟨i, by simp⟩))
  change (FinProb.pi Q).expect (fun z => g (z i)) = (Q i).expect g
  rw [hm]
  unfold FinProb.expect FinProb.pi
  -- A direct singleton-product sum avoids introducing an arbitrary inhabitant of A i.
  have hprod (z : ∀ j : {j : I // j ∈ ({i} : Finset I)}, A j.1) :
      (∏ j, (Q j.1).w (z j)) = (Q i).w (z ⟨i, by simp⟩) := by
    rw [Fintype.prod_eq_single ⟨i, by simp⟩]
    intro j hj
    have : j = ⟨i, by simp⟩ := Subtype.ext (by simpa only [Finset.mem_singleton] using j.2)
    exact (hj this).elim
  simp_rw [hprod]
  let ev : (∀ j : {j : I // j ∈ ({i} : Finset I)}, A j.1) ≃ A i :=
    { toFun := fun z => z ⟨i, by simp⟩
      invFun := fun a j => by
        have hji : j.1 = i := Finset.mem_singleton.mp j.2
        exact Eq.mp (congrArg A hji.symm) a
      left_inv := by intro z; funext j; have hj : j = ⟨i, by simp⟩ := Subtype.ext (by simpa only [Finset.mem_singleton] using j.2); subst j; rfl
      right_inv := by intro a; rfl }
  exact ev.sum_comp (fun a => (Q i).w a * g a)

private theorem E_swap {A B : Type*} [Fintype A] [Fintype B]
    (P : FinLaw A) (Q : FinLaw B) (g : A → B → ℝ) :
    P.E (fun a => Q.E (g a)) = Q.E (fun b => P.E (fun a => g a b)) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

private theorem pr_single {A : Type*} [Fintype A] (P : FinLaw A) (a : A) :
    P.pr (fun z => z = a) = P.w a := by
  classical
  simp [FinLaw.pr]

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid}

private noncomputable def prefixLaw (D : LateData hPT)
    (p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (m : ℕ) (hm : m ≤ D.geom.r) :
    FinLaw (D.encoding.base.History ⟨m, Nat.lt_succ_of_le hm⟩) :=
  FinLaw.map (FinLaw.bind (D.encoding.initialLaw D.encoding.iidLaw)
    (fun x => D.encoding.base.runFrom (kernelsFromProfiles D p).referenceTransition
      (D.encoding.initialState x) m hm)) Prod.snd

private theorem prefixLaw_step (D : LateData hPT)
    (p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (m : ℕ) (hm : m + 1 ≤ D.geom.r)
    (g : D.encoding.base.History ⟨m+1, Nat.lt_succ_of_le hm⟩ → ℝ) :
    (prefixLaw D p (m+1) hm).E g =
      (prefixLaw D p m (Nat.le_of_succ_le hm)).E (fun h =>
        ((kernelsFromProfiles D p).referenceTransition ⟨m, hm⟩ h).E
          (fun out => g (D.encoding.base.extend ⟨m, hm⟩ h out))) := by
  simp only [prefixLaw, E_map, E_bind, LateProcessBase.runFrom]

private theorem runFrom_congr (D : LateData hPT)
    (p q : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (m : ℕ) (hm : m ≤ D.geom.r)
    (hpq : ∀ j : Fin D.geom.r, j.val < m → ∀ b ∈ D.encoding.base.classes j,
      p b = q b) (s : Config D.fresh) :
    D.encoding.base.runFrom (kernelsFromProfiles D p).referenceTransition s m hm =
      D.encoding.base.runFrom (kernelsFromProfiles D q).referenceTransition s m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [LateProcessBase.runFrom, LateProcessBase.runFrom,
      ih (Nat.le_of_succ_le hm) (fun j hj => hpq j (by omega))]
    congr 2
    funext h
    unfold LateKernels.referenceTransition
    congr 1
    funext b
    change explicitRowKernel D ⟨m,hm⟩ b.1 b.2 h (p b.1) =
      explicitRowKernel D ⟨m,hm⟩ b.1 b.2 h (q b.1)
    rw [hpq ⟨m,hm⟩ (by simp) b.1 b.2]

private theorem prefixLaw_congr (D : LateData hPT)
    (p q : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (m : ℕ) (hm : m ≤ D.geom.r)
    (hpq : ∀ j : Fin D.geom.r, j.val < m → ∀ b ∈ D.encoding.base.classes j,
      p b = q b) : prefixLaw D p m hm = prefixLaw D q m hm := by
  unfold prefixLaw
  congr 2
  funext x
  exact runFrom_congr D p q m hm hpq (D.encoding.initialState x)

private theorem extend_past (D : LateData hPT) (m : Fin D.geom.r)
    (h : D.encoding.base.History m.castSucc) (out : D.encoding.base.ClassRows m)
    (j : Fin D.geom.r) (hj : j.val < m.val) :
    D.pastRows (D.encoding.base.extend m h out) j (by exact Nat.lt_trans hj (Nat.lt_succ_self _)) =
      D.pastRows h j hj := by
  funext b
  dsimp [LateData.pastRows, LateProcessBase.extend]
  rw [dif_pos (D.class_before j m.castSucc hj b.2)]

private theorem extend_current (D : LateData hPT) (m : Fin D.geom.r)
    (h : D.encoding.base.History m.castSucc) (out : D.encoding.base.ClassRows m) :
    D.pastRows (D.encoding.base.extend m h out) m (Nat.lt_succ_self _) = out := by
  funext b
  have hnot : b.1 ∉ D.encoding.base.processed m.castSucc :=
    fun hb => Finset.disjoint_left.mp (D.encoding.base.class_fresh m) b.2 hb
  dsimp [LateData.pastRows, LateProcessBase.extend]
  rw [dif_neg hnot]

private noncomputable def nextProfiles (D : LateData hPT)
    (p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (j : Fin D.geom.r) (history : FinLaw (D.encoding.base.History j.castSucc)) :
    ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b) := fun b =>
  if hb : b ∈ D.encoding.base.classes j then
    (exists_row_balanced_profile D j b hb history).choose
  else p b

private theorem nextProfiles_past (D : LateData hPT)
    (p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (j : Fin D.geom.r) (history : FinLaw (D.encoding.base.History j.castSucc))
    (t : Fin D.geom.r) (ht : t.val < j.val) (b : Pos T k)
    (hb : b ∈ D.encoding.base.classes t) : nextProfiles D p j history b = p b := by
  have hne : t ≠ j := fun he => by simpa [he] using ht
  have hnot : b ∉ D.encoding.base.classes j := fun hj =>
    Finset.disjoint_left.mp (D.encoding.base.class_disjoint t j hne) hb hj
  simp [nextProfiles, hnot]

private theorem fixedMask_weight (D : LateData hPT) (j : Fin D.geom.r)
    (b : Pos T k) (hb : b ∈ D.encoding.base.classes j)
    (history : FinLaw (D.encoding.base.History j.castSucc))
    (mask : D.encoding.base.AllowedMask b)
    (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b}) :
    (rowFixedMaskLabelLaw D j b hb history mask).w y =
      history.E (fun h => (rowSketchLaw D j b h).E (fun sketch =>
        (lateLabelLaw D j (rowSide D j b hb mask sketch) Finset.univ
          (allowedMask_nonempty D j b hb mask)).E (fun z => if z = y then 1 else 0))) := by
  rw [← pr_single, pr_eq_E]
  simp only [rowFixedMaskLabelLaw, rowSketchLabelJoint, E_map, E_bind]
  congr 1
  funext h
  congr 1
  funext sketch
  congr 1
  funext z
  by_cases he : z = y <;> simp [he]

private theorem balanced_row_E (D : LateData hPT)
    (p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (j : Fin D.geom.r) (history : FinLaw (D.encoding.base.History j.castSucc))
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k)) :
    history.E (fun h =>
      ((kernelsFromProfiles D (nextProfiles D p j history)).refK j b h).E
        (fun out => if D.encoding.base.rowLabel out = y then 1 else 0)) ≤
      2 / ((D.encoding.base.latePool j).card : ℝ) := by
  have hclass := (D.encoding.base.class_of_spec b.1 j).1 b.2
  have hpool : D.encoding.base.latePoolOf b.1 = D.encoding.base.latePool j := by
    simp [LateProcessBase.latePoolOf, hclass]
  by_cases hy : y ∈ D.encoding.base.latePoolOf b.1
  · let z : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1} := ⟨y,hy⟩
    have hbalance := (exists_row_balanced_profile D j b.1 b.2 history).choose_spec z
    change history.E (fun h =>
      (explicitRowKernel D j b.1 b.2 h (nextProfiles D p j history b.1)).E _) ≤ _
    simp only [explicitRowKernel, E_bind]
    rw [E_swap]
    have hind (label : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1}) :
        (if label.1 = y then (1 : ℝ) else 0) = if label = z then 1 else 0 := by
      have he : label.1 = y ↔ label = z := ⟨fun he => Subtype.ext he, fun he => congrArg Subtype.val he⟩
      simp only [he]
    simp only [LateProcessBase.rowLabel]
    simp_rw [hind, ← fixedMask_weight D j b.1 b.2 history]
    simpa only [FinLaw.E, nextProfiles, dif_pos b.2, hpool] using hbalance
  · have hzero (out : D.encoding.base.RowOut b.1) :
        (if D.encoding.base.rowLabel out = y then (1 : ℝ) else 0) = 0 := by
      have hn : D.encoding.base.rowLabel out ≠ y := fun he => hy (he ▸ out.2.2.2)
      simp [hn]
    simp_rw [hzero, E_const]
    positivity

private def PrefixBalanced (D : LateData hPT)
    (p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b))
    (m : ℕ) (hm : m ≤ D.geom.r) : Prop :=
  ∀ (j : Fin D.geom.r) (hj : j.val < m)
    (b : {b : Pos T k // b ∈ D.encoding.base.classes j}) (y : Fin (T.S.N k)),
    (prefixLaw D p m hm).E (fun h =>
      if D.encoding.base.rowLabel (D.pastRows h j hj b) = y then 1 else 0) ≤
      2 / ((D.encoding.base.latePool j).card : ℝ)

private theorem profiles_exist (D : LateData hPT) : ∀ m (hm : m ≤ D.geom.r),
    ∃ p : ∀ b : Pos T k, FinLaw (D.encoding.base.AllowedMask b), PrefixBalanced D p m hm := by
  intro m
  induction m with
  | zero =>
    intro hm
    refine ⟨fun b => FinLaw.dirac ⟨D.encoding.base.latePoolOf b, Finset.Subset.rfl, by omega⟩, ?_⟩
    intro j hj
    omega
  | succ m ih =>
    intro hm
    obtain ⟨p, hp⟩ := ih (Nat.le_of_succ_le hm)
    let j : Fin D.geom.r := ⟨m,hm⟩
    let history := prefixLaw D p m (Nat.le_of_succ_le hm)
    let q := nextProfiles D p j history
    have hprefix : prefixLaw D q m (Nat.le_of_succ_le hm) = history := by
      exact prefixLaw_congr D q p m (Nat.le_of_succ_le hm)
        (fun t ht b hb => nextProfiles_past D p j history t ht b hb)
    refine ⟨q, ?_⟩
    intro t ht b y
    rw [prefixLaw_step]
    by_cases htm : t.val < m
    · have hpast (h : D.encoding.base.History j.castSucc) (out : D.encoding.base.ClassRows j) :
        D.pastRows (D.encoding.base.extend j h out) t ht = D.pastRows h t htm :=
          extend_past D j h out t htm
      dsimp only [j] at hpast
      simp only [hpast, E_const]
      rw [hprefix]
      exact hp t htm b y
    · have hteq : t = j := Fin.ext (by dsimp [j]; omega)
      subst t
      have hext := extend_current D (⟨m,hm⟩ : Fin D.geom.r)
      dsimp only [j]
      simp only [hext]
      have hmarg (h : D.encoding.base.History j.castSucc) :
          ((kernelsFromProfiles D q).referenceTransition ⟨m,hm⟩ h).E
              (fun out => if D.encoding.base.rowLabel (out b) = y then (1:ℝ) else 0) =
            ((kernelsFromProfiles D q).refK ⟨m,hm⟩ b h).E
              (fun out => if D.encoding.base.rowLabel out = y then 1 else 0) := by
        convert E_pi_eval (fun c => (kernelsFromProfiles D q).refK ⟨m,hm⟩ c h) b
          (fun out : D.encoding.base.RowOut b.1 => if D.encoding.base.rowLabel out = y then (1:ℝ) else 0) using 1
        congr 1
      simp only [hmarg]
      rw [hprefix]
      exact balanced_row_E D p j history b y

/-- Class-ordered minimax selection, with each earlier marginal preserved by extension. -/
theorem balanced_kernels (D : LateData hPT) (hD : D.Spec) :
    ∃ K : LateKernels D.encoding.base,
      (D.withKernels K).Spec ∧ TransitionData (D.withKernels K) ∧ MaskBalance (D.withKernels K) := by
  obtain ⟨p,hp⟩ := profiles_exist D D.geom.r le_rfl
  refine ⟨kernelsFromProfiles D p, withKernels_spec D hD _, transitionData_of_profiles D p, ?_⟩
  intro j b y
  have hh := hp j j.isLt b y
  change (D.withKernels (kernelsFromProfiles D p)).encoding.baseline.pr _ ≤ _
  rw [pr_eq_E]
  classical
  simp only [prefixLaw, E_map] at hh
  convert hh using 1
  · congr 1
    funext z
    simp [LateData.withKernels, LateData.pastRows]
  · rfl


private theorem E_sum {A I : Type*} [Fintype A] [Fintype I] (P : FinLaw A) (g : I → A → ℝ) :
    P.E (fun a => ∑ i, g i a) = ∑ i, P.E (g i) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem E_mul_const {A : Type*} [Fintype A] (P : FinLaw A) (g : A → ℝ) (c : ℝ) :
    P.E (fun a => g a * c) = P.E g * c := by
  unfold FinLaw.E
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem E_div {A : Type*} [Fintype A] (P : FinLaw A) (g : A → ℝ) (c : ℝ) :
    P.E (fun a => g a / c) = P.E g / c := by
  simp only [div_eq_mul_inv, E_mul_const]

private theorem E_mono {A : Type*} [Fintype A] (P : FinLaw A) {f g : A → ℝ}
    (hfg : ∀ a, f a ≤ g a) : P.E f ≤ P.E g := by
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (hfg a) (P.nonneg a)

private theorem E_pi_independent {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)] (P : ∀ i, FinLaw (A i))
    (f g : (∀ i, A i) → ℝ) (s t : Finset I)
    (hf : DependsOn f (s : Set I)) (hg : DependsOn g (t : Set I)) (hst : Disjoint s t) :
    (FinLaw.pi P).E (fun z => f z * g z) = (FinLaw.pi P).E f * (FinLaw.pi P).E g := by
  let Q : ∀ i, FinProb (A i) := fun i => ⟨(P i).w,(P i).nonneg,(P i).sum_one⟩
  exact FinProb.pi_expect_mul_of_disjoint Q f g s t hf hg hst

private theorem E_pi_pair {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (P : FinLaw A) (i j : I) (hij : i ≠ j) (g : A → A → ℝ) :
    (FinLaw.pi fun _ : I => P).E (fun z => g (z i) (z j)) =
      ∑ x, ∑ y, P.w x * P.w y * g x y := by
  classical
  let Q := FinLaw.pi fun _ : I => P
  let ind : I → A → (I → A) → ℝ := fun i x z => if z i = x then 1 else 0
  have hi (i : I) (x : A) : Q.E (ind i x) = P.w x := by
    have hmarg := E_pi_eval (fun _ : I => P) i (fun a => if a=x then (1:ℝ) else 0)
    calc
      Q.E (ind i x) = P.E (fun a => if a=x then (1:ℝ) else 0) := hmarg
      _ = P.w x := by simp [FinLaw.E,eq_comm]
  have hp (x y : A) : Q.E (fun z => ind i x z * ind j y z) = P.w x * P.w y := by
    rw [E_pi_independent (fun _ : I => P) (ind i x) (ind j y) {i} {j}]
    · rw [hi,hi]
    · intro z z' hh
      change (if z i = x then (1:ℝ) else 0) = if z' i = x then 1 else 0
      rw [hh i (by simp)]
    · intro z z' hh
      change (if z j = y then (1:ℝ) else 0) = if z' j = y then 1 else 0
      rw [hh j (by simp)]
    · simpa using hij
  have he (z : I → A) : g (z i) (z j) =
      ∑ x, ∑ y, (ind i x z * ind j y z) * g x y := by
    simp [ind,ite_mul,mul_ite,eq_comm]
  dsimp only [Q] at hp
  simp only [he,E_sum,E_mul_const,hp]

noncomputable def conflictFraction {A : Type*} {m : ℕ} (R : A → A → Prop) (z : Fin m → A) : ℝ :=
  (∑ i, ∑ j, if R (z i) (z j) then (1:ℝ) else 0) / (m:ℝ)^2

/-- The diagonal contributes at most 1/m; off-diagonal samples are independent. -/
theorem conflictFraction_mean {A : Type*} [Fintype A] (P : FinLaw A)
    (R : A → A → Prop) (m : ℕ) (hm : 0 < m) (q : ℝ) (hq : 0 ≤ q)
    (hrow : ∀ x, (∑ y, P.w y * (if R x y then (1:ℝ) else 0)) ≤ q) :
    (FinLaw.pi fun _ : Fin m => P).E (conflictFraction R) ≤ 1/(m:ℝ) + q := by
  classical
  let Q := FinLaw.pi fun _ : Fin m => P
  have hpair (i j : Fin m) : Q.E (fun z => if R (z i) (z j) then (1:ℝ) else 0) ≤
      (if i=j then 1 else 0) + q := by
    by_cases hij : i = j
    · have hh := E_mono Q (f := fun z => if R (z i) (z j) then (1:ℝ) else 0)
        (g := fun _ => (1:ℝ)) (fun z => by split_ifs <;> norm_num)
      rw [E_const] at hh
      simp only [hij,ite_true]
      simpa only [hij] using hh.trans (show (1:ℝ) ≤ 1+q by linarith)
    · have hh := E_pi_pair P i j hij (fun x y => if R x y then (1:ℝ) else 0)
      rw [hh,if_neg hij,zero_add]
      calc
        (∑ x, ∑ y, P.w x * P.w y * (if R x y then (1:ℝ) else 0)) =
            ∑ x, P.w x * (∑ y, P.w y * (if R x y then (1:ℝ) else 0)) := by
          simp only [Finset.mul_sum,mul_assoc]
        _ ≤ ∑ x, P.w x * q := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hrow x) (P.nonneg x)
        _ = q := by rw [← Finset.sum_mul,P.sum_one,one_mul]
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  unfold conflictFraction
  rw [E_div]
  simp_rw [E_sum]
  apply (div_le_iff₀ (sq_pos_of_pos hm')).mpr
  calc
    (∑ i, ∑ j, Q.E (fun z => if R (z i) (z j) then (1:ℝ) else 0)) ≤
        ∑ i : Fin m, ∑ j : Fin m, ((if i=j then (1:ℝ) else 0) + q) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = (1/(m:ℝ)+q) * (m:ℝ)^2 := by
      simp [Finset.sum_add_distrib,eq_comm]
      field_simp

/-- Replacing one sample affects at most two rows of the ordered pair sum. -/
theorem conflictFraction_lipschitz {A : Type*} (R : A → A → Prop) (m : ℕ) (hm : 0 < m)
    (p : Fin m) (z z' : Fin m → A) (h : ∀ i, i ≠ p → z i = z' i) :
    |conflictFraction R z - conflictFraction R z'| ≤ 2/(m:ℝ) := by
  classical
  let f := fun (z : Fin m → A) (i j : Fin m) => if R (z i) (z j) then (1:ℝ) else 0
  have hb (i j : Fin m) : |f z i j - f z' i j| ≤
      (if i=p then (1:ℝ) else 0) + (if j=p then 1 else 0) := by
    by_cases hi : i=p <;> by_cases hj : j=p
    · dsimp [f]; split_ifs <;> norm_num
    · dsimp [f]; simp only [if_pos hi,if_neg hj]; split_ifs <;> norm_num
    · dsimp [f]; simp only [if_neg hi,if_pos hj]; split_ifs <;> norm_num
    · simp only [f,h i hi,h j hj,sub_self,abs_zero,if_neg hi,if_neg hj,add_zero,le_refl]
  have hsum : |(∑ i, ∑ j, f z i j) - (∑ i, ∑ j, f z' i j)| ≤ 2*(m:ℝ) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |∑ j, (f z i j - f z' i j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |f z i j - f z' i j| := Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, ((if i=p then (1:ℝ) else 0) + (if j=p then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
      _ = 2*(m:ℝ) := by simp [Finset.sum_add_distrib]; ring
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  unfold conflictFraction
  rw [← sub_div,abs_div,abs_of_pos (sq_pos_of_pos hm')]
  calc
    _ ≤ (2*(m:ℝ))/(m:ℝ)^2 := div_le_div_of_nonneg_right hsum (sq_nonneg _)
    _ = 2/(m:ℝ) := by field_simp

/-- A tail bound for the actual ordered conflicting-pair statistic. -/
theorem conflictFraction_tail {A : Type*} [Fintype A] (P : FinLaw A)
    (R : A → A → Prop) (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ)
    (hmean : (FinLaw.pi fun _ : Fin m => P).E (conflictFraction R) ≤ δ) :
    (FinLaw.pi fun _ : Fin m => P).pr (fun z => 2*δ ≤ conflictFraction R z) ≤
      2 * Real.exp (-(m:ℝ) * δ^2 / 2) := by
  let Q : FinProb A := ⟨P.w,P.nonneg,P.sum_one⟩
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hwidth : (∑ i : Fin m, (2/(m:ℝ))^2) = 4/(m:ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
    ring
  have hh := bounded_difference_upper_tail (fun _ : Fin m => Q) (conflictFraction R)
    (fun _ => 2/(m:ℝ)) (fun _ => by positivity)
    (conflictFraction_lipschitz R m hm) (by rw [hwidth]; positivity) δ hδ hmean
  change (FinLaw.pi fun _ : Fin m => P).pr _ ≤ _ at hh
  rw [hwidth] at hh
  convert hh using 1
  congr 2
  field_simp
  ring


private theorem pr_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (P : FinLaw A) (B : I → A → Prop) : P.pr (fun a => ∃ i, B i a) ≤ ∑ i, P.pr (B i) := by
  classical
  simp only [pr_eq_E]
  rw [← E_sum]
  apply E_mono
  intro a
  by_cases hex : ∃ i, B i a
  · obtain ⟨i,hi⟩ := hex
    simp only [if_pos (show ∃ i, B i a from ⟨i,hi⟩)]
    calc
      (1:ℝ) = if B i a then 1 else 0 := by simp [hi]
      _ ≤ ∑ j, if B j a then (1:ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if B j a then (1:ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · simp only [if_neg hex]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

private noncomputable def sketchBad (D : LateData hPT) (j : Fin D.geom.r) (b : Pos T k)
    (sketch : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) : Prop :=
  ∃ a, 2 * D.error (flipPos b a) j ^ 4 <
    conflictFraction (fun x z => ¬ D.nonconflict (flipPos b a) x z) (sketch a)

private theorem R1_iff_sketch (D : LateData hPT) (j : Fin D.geom.r) (b : Pos T k)
    (out : D.encoding.base.RowOut b) : ¬ D.R1 j out ↔ sketchBad D j b out.2.1 := by
  simp only [LateData.R1,sketchBad,conflictFraction,not_forall,not_le]
  congr!

private theorem refK_eq_explicit (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) :
    D.encoding.kernels.refK j b h = explicitRowKernel D j b.1 b.2 h (D.encoding.kernels.maskProfile b.1) := by
  apply finLaw_eq_of_weights
  intro out
  rw [hT.reference_formula,explicitRowKernel_formula]
  rfl

private theorem refK_sketchBad (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) :
    (D.encoding.kernels.refK j b h).pr (fun out => ¬ D.R1 j out) =
      (rowSketchLaw D j b.1 h).pr (sketchBad D j b.1) := by
  rw [refK_eq_explicit D hT,pr_eq_E,pr_eq_E]
  simp only [explicitRowKernel,E_bind]
  have hind (mask : D.encoding.base.AllowedMask b.1)
      (sketch : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k))
      (y : {y : Fin (T.S.N k) // y ∈ D.encoding.base.latePoolOf b.1}) :
      (if ¬ D.R1 j (mask,sketch,y) then (1:ℝ) else 0) =
        if sketchBad D j b.1 sketch then 1 else 0 := by
    simp only [R1_iff_sketch]
  have hinner (mask : D.encoding.base.AllowedMask b.1)
      (sketch : Fin (T.S.n k) → Fin (sketchLength T k) → Fin (T.S.N k)) :
      (lateLabelLaw D j (rowSide D j b.1 b.2 mask sketch) Finset.univ
        (allowedMask_nonempty D j b.1 b.2 mask)).E
          (fun y => if ¬ D.R1 j (mask,sketch,y) then (1:ℝ) else 0) =
        if sketchBad D j b.1 sketch then 1 else 0 := by
    calc
      _ = (lateLabelLaw D j (rowSide D j b.1 b.2 mask sketch) Finset.univ
          (allowedMask_nonempty D j b.1 b.2 mask)).E
            (fun _ => if sketchBad D j b.1 sketch then (1:ℝ) else 0) := by
        congr 1
        funext y
        exact hind mask sketch y
      _ = _ := E_const _ _
  calc
    _ = (D.encoding.kernels.maskProfile b.1).E
        (fun _ => (rowSketchLaw D j b.1 h).E
          (fun sketch => if sketchBad D j b.1 sketch then (1:ℝ) else 0)) := by
      congr 1
      funext mask
      congr 1
      funext sketch
      convert hinner mask sketch using 1
      congr 1
      funext y
      by_cases hh : ¬ D.R1 j (mask,sketch,y) <;> simp [hh]
    _ = _ := E_const _ _

/-- Requirement 1 for the exact row kernel reduces to the actual sketch means. -/
theorem R1_tail_from_means (D : LateData hPT) (hT : TransitionData D)
    (j : Fin D.geom.r) (b : {b : Pos T k // b ∈ D.encoding.base.classes j})
    (h : D.encoding.base.History j.castSucc) (hm : 0 < sketchLength T k)
    (hmean : ∀ a,
      (FinLaw.pi fun _ : Fin (sketchLength T k) => asFinLaw (D.currentPrior j (flipPos b.1 a) h)).E
        (conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z)) ≤
          D.error (flipPos b.1 a) j ^ 4) :
    (D.encoding.kernels.refK j b h).pr (fun out => ¬ D.R1 j out) ≤
      ∑ a : Fin (T.S.n k), 2 * Real.exp (-(sketchLength T k : ℝ) * D.error (flipPos b.1 a) j ^ 8 / 2) := by
  rw [refK_sketchBad D hT]
  apply (pr_exists_le (rowSketchLaw D j b.1 h) _).trans
  apply Finset.sum_le_sum
  intro a _
  let P := asFinLaw (D.currentPrior j (flipPos b.1 a) h)
  have hproj : (rowSketchLaw D j b.1 h).pr
      (fun sketch => 2 * D.error (flipPos b.1 a) j ^ 4 <
        conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z) (sketch a)) =
      (FinLaw.pi fun _ : Fin (sketchLength T k) => P).pr
        (fun sketch => 2 * D.error (flipPos b.1 a) j ^ 4 <
          conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z) sketch) := by
    simp only [pr_eq_E,rowSketchLaw]
    convert E_pi_eval
      (fun a => FinLaw.pi fun _ : Fin (sketchLength T k) => asFinLaw (D.currentPrior j (flipPos b.1 a) h)) a
      (fun sketch => if 2 * D.error (flipPos b.1 a) j ^ 4 <
          conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z) sketch then (1:ℝ) else 0) using 1
  rw [hproj]
  have hδ : 0 < D.error (flipPos b.1 a) j ^ 4 := pow_pos
    (lateError_pos (D.geom.patchOf (flipPos b.1 a)) (D.geom.r-j.val)) 4
  have hh := conflictFraction_tail P (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z)
    (sketchLength T k) hm (D.error (flipPos b.1 a) j ^ 4) hδ (hmean a)
  have hmono : (FinLaw.pi fun _ : Fin (sketchLength T k) => P).pr
      (fun sketch => 2 * D.error (flipPos b.1 a) j ^ 4 <
        conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z) sketch) ≤
      (FinLaw.pi fun _ : Fin (sketchLength T k) => P).pr
      (fun sketch => 2 * D.error (flipPos b.1 a) j ^ 4 ≤
        conflictFraction (fun x z => ¬ D.nonconflict (flipPos b.1 a) x z) sketch) := by
    simp only [pr_eq_E]
    apply E_mono
    intro sketch
    split_ifs <;> try norm_num <;> linarith
  exact hmono.trans (by simpa only [← pow_mul] using hh)

end HypercubeRamsey.Lane_sol_s18_n1
