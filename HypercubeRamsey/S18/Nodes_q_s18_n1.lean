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
