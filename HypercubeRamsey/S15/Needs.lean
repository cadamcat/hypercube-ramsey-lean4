import HypercubeRamsey.PartC.All
import HypercubeRamsey.Framework.LawLemmas

/-!
Contracts requested from the Section 12 producer. Those modules are not on this branch yet; these declarations
give the proof lanes for Section 15 a stable finite-law interface to request during integration.
-/

namespace HypercubeRamsey.S15.Needs

open HypercubeRamsey Filter
open Classical
open scoped BigOperators

variable {N : ℕ}

/-- D12.0: the centered normalized-hit coefficient, used only on positive degree gates. -/
noncomputable def acoef (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    (x y : Fin N) : ℝ :=
  let d := deg E c π x
  if 0 < d then hit E c x y / d - 1 else -1

/-- D12.0: a joint interaction of a law with centered coefficients. -/
noncomputable def inter (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    {u : ℕ} (J : Finset (Fin u)) (xs : Fin u → Fin N) : ℝ :=
  ∑ y, π y * ∏ i ∈ J, acoef E c π (xs i) y

/-- D12.0: product weight of a tuple under a finite product law. -/
noncomputable def prodW {u : ℕ} (τ : Fin N → ℝ) (xs : Fin u → Fin N) : ℝ :=
  ∏ i, τ (xs i)

/-- D12.0: the positive product term in the centered-moment expansion. -/
noncomputable def posTerm (E : Fin N → Fin N → Prop) (c : Colour)
    {d u : ℕ} (π : Fin d → Fin N → ℝ) (I : Finset (Fin u))
    (xs : Fin u → Fin N) : ℝ :=
  ∏ l, ∑ y, π l y * ∏ i ∈ I, (1 + acoef E c (π l) (xs i) y)

/-- D12.0: the signed integrand in equation (15.10). -/
noncomputable def Phi (E : Fin N → Fin N → Prop) (c : Colour)
    {d u : ℕ} (π : Fin d → Fin N → ℝ) (xs : Fin u → Fin N) : ℝ :=
  ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) * posTerm E c π I xs

/-- D12.0: all interactions on a tuple are at most `t`. -/
def Moderate (E : Fin N → Fin N → Prop) (c : Colour)
    {d u : ℕ} (π : Fin d → Fin N → ℝ) (t : ℝ) (xs : Fin u → Fin N) : Prop :=
  ∀ l (J : Finset (Fin u)), 2 ≤ J.card → |inter E c (π l) J xs| ≤ t

/-- D12.0: common-neighbour mass after heterogeneous odd labels. -/
noncomputable def Zmass (E : Fin N → Fin N → Prop) (c : Colour)
    {d : ℕ} (τ : Fin N → ℝ) (π : Fin d → Fin N → ℝ) (ys : Fin d → Fin N) : ℝ :=
  ∑ x, τ x * ∏ l, (1 + acoef E c (π l) x (ys l))

/-- D12.0: degree gate used by the interaction estimates. -/
def DegGate (E : Fin N → Fin N → Prop) (c : Colour) (π : Fin N → ℝ)
    (C0 b : ℝ) (x : Fin N) : Prop := |deg E c π x - 1 / 2| ≤ C0 * b

/-- D12.0: heterogeneous laws and a small-width first law for Section 12. -/
structure InterSetting (T : Stage) (k : ℕ) (xs4 : ℝ) where
  d : ℕ
  d_le : d ≤ T.S.n k
  τ : Law (T.S.N k)
  π : Fin d → Law (T.S.N k)
  τ_supported : τ.SupportedIn (T.X k)
  π_supported : ∀ l, (π l).SupportedIn (T.Y k)
  τ_width : τ.WidthLE ((T.S.n k : ℝ) ^ xs4)
  π_width : ∀ l, (π l).WidthLE ((T.S.n k : ℝ) ^ xs4)

/-- D12.0: degree gates hold on the support of `τ`. -/
def InterSetting.DegOK {T : Stage} {k : ℕ} {xs4 : ℝ}
    (S : InterSetting T k xs4) (c : Colour) (C0 : ℝ) : Prop :=
  ∀ l x, 0 < S.τ.w x → DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) x

/-- SHARED: L12.0(a), deep discrepancy bounds the first-side degree-outlier mass. -/
theorem exceptional_first {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w1 W2 w : ℝ}
    (hpair : (w1 ≤ wS ∧ W2 ≤ wL) ∨ (w1 ≤ wL ∧ W2 ≤ wS))
    (ν τ : Law (T.S.N k)) (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w1)
    (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w) :
    ∑ x ∈ Finset.univ.filter fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|, τ.w x ≤
      2 * Real.exp (w - W2) := by
  classical
  let q : Fin (T.S.N k) → ℝ := fun x => deg (T.S.E k) c ν.w x - 1 / 2
  let B := Finset.univ.filter fun x => err < |q x|
  let P := B.filter fun x => 0 ≤ q x
  let M := B.filter fun x => q x < 0
  have cond_supported (S : Finset (Fin (T.S.N k)))
      (hm : 0 < ∑ x ∈ S, τ.w x) : (τ.cond S hm).SupportedIn (T.X k) := by
    intro x hx
    simp [Law.cond, Law.restrict, hτ x hx]
  have cond_width (S : Finset (Fin (T.S.N k)))
      (hm : 0 < ∑ x ∈ S, τ.w x)
      (hmexp : Real.exp (w - W2) < ∑ x ∈ S, τ.w x) :
      (τ.cond S hm).WidthLE W2 := by
    have hlog : w - W2 < Real.log (∑ x ∈ S, τ.w x) := by
      have h := Real.log_lt_log (Real.exp_pos (w - W2)) hmexp
      simpa using h
    have hrestr := Law.WidthLE.restrict hτw hm
    have hcond : (τ.cond S hm).WidthLE (w - Real.log (∑ x ∈ S, τ.w x)) := by
      simpa [Law.cond] using hrestr
    exact Law.WidthLE.mono hcond (by linarith)
  have dens_eq_row (μ : Law (T.S.N k)) :
      dens (T.S.E k) c μ ν = ∑ x, μ.w x * deg (T.S.E k) c ν.w x := by
    simp only [dens, deg, hit]
    calc
      ∑ x, ∑ y, μ.w x * ν.w y * (if Hits (T.S.E k) c x y then 1 else 0) =
          ∑ y, ∑ x, μ.w x * (ν.w y * (if Hits (T.S.E k) c x y then 1 else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ x, μ.w x * ∑ y, ν.w y *
          (if Hits (T.S.E k) c x y then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
          (fun y => ν.w y * (if Hits (T.S.E k) c x y then 1 else 0)) (μ.w x)).symm
  have qmean (μ : Law (T.S.N k)) :
      ∑ x, μ.w x * q x = dens (T.S.E k) c μ ν - 1 / 2 := by
    calc
      ∑ x, μ.w x * q x =
          ∑ x, (μ.w x * deg (T.S.E k) c ν.w x - μ.w x * (1 / 2)) := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [q]
        ring
      _ = (∑ x, μ.w x * deg (T.S.E k) c ν.w x) -
            (∑ x, μ.w x * (1 / 2)) := by
        simpa using (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset (Fin (T.S.N k))))
          (fun x => μ.w x * deg (T.S.E k) c ν.w x)
          (fun x => μ.w x * (1 / 2)))
      _ = dens (T.S.E k) c μ ν - 1 / 2 := by
        have hhalf : ∑ x, μ.w x * (1 / 2) = 1 / 2 := by
          calc
            ∑ x, μ.w x * (1 / 2) = (∑ x, μ.w x) * (1 / 2) := by
              simpa using (Finset.sum_mul (Finset.univ : Finset (Fin (T.S.N k)))
                (fun x => μ.w x) (1 / 2)).symm
            _ = 1 / 2 := by rw [μ.sum_eq_one]; norm_num
        rw [hhalf, ← dens_eq_row μ]
  have has_pos_mass (μ : Law (T.S.N k)) : ∃ x, 0 < μ.w x := by
    by_contra h
    push_neg at h
    have hz : ∀ x, μ.w x = 0 := fun x =>
      le_antisymm (h x) (μ.nonneg x)
    have hs : (∑ x, μ.w x) = 0 := by simp [hz]
    rw [μ.sum_eq_one] at hs
    norm_num at hs
  have side_bound (S : Finset (Fin (T.S.N k))) (s : ℝ)
      (hs : s = 1 ∨ s = -1)
      (hmargin : ∀ x ∈ S, err < s * q x) :
      ∑ x ∈ S, τ.w x ≤ Real.exp (w - W2) := by
    by_contra hnot
    have hmass : Real.exp (w - W2) < ∑ x ∈ S, τ.w x := lt_of_not_ge hnot
    have hm : 0 < ∑ x ∈ S, τ.w x := lt_trans (Real.exp_pos _) hmass
    let μ := τ.cond S hm
    have hμs : μ.SupportedIn (T.X k) := by
      simpa [μ] using cond_supported S hm
    have hμw : μ.WidthLE W2 := by
      simpa [μ] using cond_width S hm hmass
    have hwidthPair :
        (μ.WidthLE wL ∧ ν.WidthLE wS) ∨ (μ.WidthLE wS ∧ ν.WidthLE wL) := by
      rcases hpair with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · exact Or.inl ⟨Law.WidthLE.mono hμw hw2, Law.WidthLE.mono hνw hw1⟩
      · exact Or.inr ⟨Law.WidthLE.mono hμw hw2, Law.WidthLE.mono hνw hw1⟩
    have hdisc := hD c μ ν hμs hν hwidthPair
    have hμpos := has_pos_mass μ
    have hpoint (x : Fin (T.S.N k)) (hx : 0 < μ.w x) : err < s * q x := by
      have hxS : x ∈ S := by
        by_contra hnotS
        have hzero : μ.w x = 0 := by simp [μ, Law.cond, Law.restrict, hnotS]
        rw [hzero] at hx
        norm_num at hx
      exact hmargin x hxS
    have hsumlt : ∑ x, μ.w x * err < ∑ x, μ.w x * (s * q x) := by
      apply Finset.sum_lt_sum
      · intro x hx
        by_cases hz : μ.w x = 0
        · simp [hz]
        · have hxpos : 0 < μ.w x := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hz)
          exact mul_le_mul_of_nonneg_left (le_of_lt (hpoint x hxpos)) (μ.nonneg x)
      · obtain ⟨x, hx⟩ := hμpos
        exact ⟨x, Finset.mem_univ _, mul_lt_mul_of_pos_left (hpoint x hx) hx⟩
    have hleft : ∑ x, μ.w x * err = err := by
      calc
        ∑ x, μ.w x * err = (∑ x, μ.w x) * err := by
          simpa using (Finset.sum_mul (Finset.univ : Finset (Fin (T.S.N k)))
            (fun x => μ.w x) err).symm
        _ = err := by rw [μ.sum_eq_one]; ring
    have hright : ∑ x, μ.w x * (s * q x) = s * (dens (T.S.E k) c μ ν - 1 / 2) := by
      calc
        ∑ x, μ.w x * (s * q x) = s * ∑ x, μ.w x * q x := by
          calc
            ∑ x, μ.w x * (s * q x) = ∑ x, s * (μ.w x * q x) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = s * ∑ x, μ.w x * q x := by
              simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
                (fun x => μ.w x * q x) s).symm
        _ = s * (dens (T.S.E k) c μ ν - 1 / 2) := by rw [qmean]
    have hmean : err < s * (dens (T.S.E k) c μ ν - 1 / 2) := by
      rw [hleft] at hsumlt
      rw [hright] at hsumlt
      exact hsumlt
    have herr : 0 ≤ err := le_trans (abs_nonneg _) hdisc
    have hsignbound : s * (dens (T.S.E k) c μ ν - 1 / 2) ≤
        |dens (T.S.E k) c μ ν - 1 / 2| := by
      rcases hs with hs | hs
      · rw [hs]
        simpa using le_abs_self (dens (T.S.E k) c μ ν - 1 / 2)
      · rw [hs]
        simpa using neg_le_abs (dens (T.S.E k) c μ ν - 1 / 2)
    linarith
  have hPmargin : ∀ x ∈ P, err < (1 : ℝ) * q x := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxB, hq⟩
    have hbad : err < |q x| := (Finset.mem_filter.mp hxB).2
    simpa [abs_of_nonneg hq] using hbad
  have hMmargin : ∀ x ∈ M, err < (-1 : ℝ) * q x := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxB, hq⟩
    have hbad : err < |q x| := (Finset.mem_filter.mp hxB).2
    simpa [abs_of_neg hq] using hbad
  have hP := side_bound P 1 (Or.inl rfl) hPmargin
  have hM := side_bound M (-1) (Or.inr rfl) hMmargin
  have hdisjoint : Disjoint P M := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxM
    exact (not_lt_of_ge (Finset.mem_filter.mp hxP).2) (Finset.mem_filter.mp hxM).2
  have hunion : P ∪ M = B := by
    ext x
    simp only [Finset.mem_union, P, M, B, Finset.mem_filter, Finset.mem_univ]
    constructor
    · rintro (⟨hbad, _⟩ | ⟨hbad, _⟩) <;> exact hbad
    · intro hxB
      by_cases hq : 0 ≤ q x
      · exact Or.inl ⟨hxB, hq⟩
      · exact Or.inr ⟨hxB, lt_of_not_ge hq⟩
  calc
    (∑ x ∈ Finset.univ.filter fun x => err < |deg (T.S.E k) c ν.w x - 1 / 2|, τ.w x) =
        ∑ x ∈ B, τ.w x := by simp [B, q]
    _ = (∑ x ∈ P, τ.w x) + ∑ x ∈ M, τ.w x := by
      rw [← hunion]
      exact Finset.sum_union hdisjoint
    _ ≤ Real.exp (w - W2) + Real.exp (w - W2) := add_le_add hP hM
    _ = 2 * Real.exp (w - W2) := by ring

/-- SHARED: L12.0(b), the symmetric second-side degree-outlier bound. -/
theorem exceptional_second {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w1 W2 w : ℝ}
    (hpair : (w1 ≤ wS ∧ W2 ≤ wL) ∨ (w1 ≤ wL ∧ W2 ≤ wS))
    (τ ν : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w1)
    (hν : ν.SupportedIn (T.Y k)) (hνw : ν.WidthLE w) :
    ∑ y ∈ Finset.univ.filter fun y => err < |colDeg (T.S.E k) c τ y - 1 / 2|, ν.w y ≤
      2 * Real.exp (w - W2) := by
  classical
  have hDswap : TwoBudgetDisc T.swap k wS wL err := by
    intro c' μ ν hμ hν hwidth
    let μ' : Law (T.S.N k) := by simpa [Stage.swap, BadSeq.swap] using μ
    let ν' : Law (T.S.N k) := by simpa [Stage.swap, BadSeq.swap] using ν
    have hμ' : μ'.SupportedIn (T.Y k) := by
      simpa [μ', Stage.swap, BadSeq.swap] using hμ
    have hν' : ν'.SupportedIn (T.X k) := by
      simpa [ν', Stage.swap, BadSeq.swap] using hν
    have hwidth' :
        (ν'.WidthLE wL ∧ μ'.WidthLE wS) ∨ (ν'.WidthLE wS ∧ μ'.WidthLE wL) := by
      rcases hwidth with ⟨hμw, hνw⟩ | ⟨hμw, hνw⟩
      · exact Or.inr ⟨by simpa [ν', Stage.swap, BadSeq.swap] using hνw,
          by simpa [μ', Stage.swap, BadSeq.swap] using hμw⟩
      · exact Or.inl ⟨by simpa [ν', Stage.swap, BadSeq.swap] using hνw,
          by simpa [μ', Stage.swap, BadSeq.swap] using hμw⟩
    have hbound : |dens (T.S.E k) c' ν' μ' - 1 / 2| ≤ err := by
      exact hD c' ν' μ' hν' hμ' hwidth'
    have htrans :
        |dens (transposeRel (T.S.E k)) c' μ' ν' - 1 / 2| ≤ err := by
      rw [dens_transpose]
      exact hbound
    simpa [TwoBudgetDisc, Stage.swap, BadSeq.swap, μ', ν'] using htrans
  have h := exceptional_first (T := T.swap) hDswap c hpair τ ν hτ hτw hν hνw
  convert h using 1 <;> simp [Stage.swap, BadSeq.swap, deg, colDeg, hit, hits_transpose] <;> rfl

/-- SHARED: L12.0(c), deep discrepancy bounds bounded signed degree tests. -/
theorem exceptional_signed {T : Stage} {k : ℕ} {wS wL err : ℝ}
    (hD : TwoBudgetDisc T k wS wL err) (c : Colour)
    {w1 W2 w : ℝ}
    (hpair : (w1 ≤ wS ∧ W2 ≤ wL) ∨ (w1 ≤ wL ∧ W2 ≤ wS))
    (π : Law (T.S.N k)) (hπ : π.SupportedIn (T.Y k)) (hπw : π.WidthLE (w1 - Real.log 3))
    (h : Fin (T.S.N k) → ℝ) (hh : ∀ y, |h y| ≤ 1)
    (τ : Law (T.S.N k)) (hτ : τ.SupportedIn (T.X k)) (hτw : τ.WidthLE w) :
    ∑ x ∈ Finset.univ.filter
      (fun x => 6 * err < |∑ y, π.w y * h y * (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|),
      τ.w x ≤ 4 * Real.exp (w - W2) := by
  classical
  let a : ℝ := ∑ y, π.w y * h y
  let f : Fin (T.S.N k) → ℝ := fun y => h y - a
  let r : Fin (T.S.N k) → ℝ := fun y => f y / 2
  let g : Fin (T.S.N k) → ℝ := fun x =>
    ∑ y, π.w y * h y * (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)
  let B := Finset.univ.filter fun x => 6 * err < |g x|
  let P := B.filter fun x => 0 ≤ g x
  let M := B.filter fun x => g x < 0
  have ha : |a| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · calc
        -1 = ∑ y, -π.w y := by simp [π.sum_eq_one]
        _ ≤ ∑ y, π.w y * h y := by
          apply Finset.sum_le_sum
          intro y hy
          have hy' : -1 ≤ h y := (abs_le.mp (hh y)).1
          have hmul := mul_le_mul_of_nonneg_left hy' (π.nonneg y)
          simpa using hmul
        _ = a := rfl
    · calc
        a = ∑ y, π.w y * h y := rfl
        _ ≤ ∑ y, π.w y := by
          apply Finset.sum_le_sum
          intro y hy
          simpa using mul_le_mul_of_nonneg_left (abs_le.mp (hh y)).2 (π.nonneg y)
        _ = 1 := π.sum_eq_one
  have hf (y : Fin (T.S.N k)) : |f y| ≤ 2 := by
    dsimp [f]
    apply abs_le.mpr
    have hh' := abs_le.mp (hh y)
    have ha' := abs_le.mp ha
    constructor <;> linarith
  have hr (y : Fin (T.S.N k)) : |r y| ≤ 1 := by
    dsimp [r]
    rw [abs_div]
    norm_num
    nlinarith [hf y]
  have fmean : ∑ y, π.w y * f y = 0 := by
    calc
      ∑ y, π.w y * f y = ∑ y, (π.w y * h y - a * π.w y) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [f]
        ring
      _ = (∑ y, π.w y * h y) - ∑ y, a * π.w y := by
        simpa using (Finset.sum_sub_distrib
          (s := (Finset.univ : Finset (Fin (T.S.N k))))
          (fun y => π.w y * h y) (fun y => a * π.w y))
      _ = (∑ y, π.w y * h y) - a * ∑ y, π.w y := by
        congr 1
        simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
          (fun y => π.w y) a).symm
      _ = 0 := by simp [a, π.sum_eq_one]
  have rmean : ∑ y, π.w y * r y = 0 := by
    calc
      ∑ y, π.w y * r y = ∑ y, (1 / 2) * (π.w y * f y) := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [r]
        ring
      _ = (1 / 2) * ∑ y, π.w y * f y := by
        simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
          (fun y => π.w y * f y) (1 / 2)).symm
      _ = 0 := by rw [fmean]; ring
  let rhoPlus : Law (T.S.N k) := {
    w := fun y => π.w y * (1 + r y)
    nonneg := by
      intro y
      have hr' := (abs_le.mp (hr y))
      exact mul_nonneg (π.nonneg y) (by linarith)
    sum_eq_one := by
      calc
        ∑ y, π.w y * (1 + r y) = ∑ y, (π.w y + π.w y * r y) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y, π.w y) + ∑ y, π.w y * r y := by
          simpa using (Finset.sum_add_distrib
            (s := (Finset.univ : Finset (Fin (T.S.N k)))))
        _ = 1 := by rw [π.sum_eq_one, rmean]; norm_num
  }
  let rhoMinus : Law (T.S.N k) := {
    w := fun y => π.w y * (1 - r y)
    nonneg := by
      intro y
      have hr' := (abs_le.mp (hr y))
      exact mul_nonneg (π.nonneg y) (by linarith)
    sum_eq_one := by
      calc
        ∑ y, π.w y * (1 - r y) = ∑ y, (π.w y - π.w y * r y) := by
          apply Finset.sum_congr rfl
          intro y hy
          ring
        _ = (∑ y, π.w y) - ∑ y, π.w y * r y := by
          simpa using (Finset.sum_sub_distrib
            (s := (Finset.univ : Finset (Fin (T.S.N k))))
            (fun y => π.w y) (fun y => π.w y * r y))
        _ = 1 := by rw [π.sum_eq_one, rmean]; norm_num
  }
  have hrhoPlusSupport : rhoPlus.SupportedIn (T.Y k) := by
    intro y hy
    simp [rhoPlus, hπ y hy]
  have hrhoMinusSupport : rhoMinus.SupportedIn (T.Y k) := by
    intro y hy
    simp [rhoMinus, hπ y hy]
  have hExp : 2 * Real.exp (w1 - Real.log 3) ≤ Real.exp w1 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    have he := Real.exp_pos w1
    field_simp
    linarith
  have hrhoPlusWidth : rhoPlus.WidthLE w1 := by
    intro y
    have hfactor : 0 ≤ 1 + r y ∧ 1 + r y ≤ 2 := by
      have h := abs_le.mp (hr y)
      constructor <;> linarith
    change π.w y * (1 + r y) ≤ Real.exp w1 / (T.S.N k)
    calc
      π.w y * (1 + r y) ≤ π.w y * 2 := mul_le_mul_of_nonneg_left hfactor.2 (π.nonneg y)
      _ = 2 * π.w y := by ring
      _ ≤ 2 * (Real.exp (w1 - Real.log 3) / (T.S.N k)) :=
        mul_le_mul_of_nonneg_left (hπw y) (by norm_num)
      _ = (2 * Real.exp (w1 - Real.log 3)) / (T.S.N k) := by ring
      _ ≤ Real.exp w1 / (T.S.N k) :=
        div_le_div_of_nonneg_right hExp (by positivity)
  have hrhoMinusWidth : rhoMinus.WidthLE w1 := by
    intro y
    have hfactor : 0 ≤ 1 - r y ∧ 1 - r y ≤ 2 := by
      have h := abs_le.mp (hr y)
      constructor <;> linarith
    change π.w y * (1 - r y) ≤ Real.exp w1 / (T.S.N k)
    calc
      π.w y * (1 - r y) ≤ π.w y * 2 := mul_le_mul_of_nonneg_left hfactor.2 (π.nonneg y)
      _ = 2 * π.w y := by ring
      _ ≤ 2 * (Real.exp (w1 - Real.log 3) / (T.S.N k)) :=
        mul_le_mul_of_nonneg_left (hπw y) (by norm_num)
      _ = (2 * Real.exp (w1 - Real.log 3)) / (T.S.N k) := by ring
      _ ≤ Real.exp w1 / (T.S.N k) :=
        div_le_div_of_nonneg_right hExp (by positivity)
  have dens_eq_row (μ ρ : Law (T.S.N k)) :
      dens (T.S.E k) c μ ρ = ∑ x, μ.w x * ∑ y, ρ.w y * hit (T.S.E k) c x y := by
    simp only [dens, hit]
    calc
      ∑ x, ∑ y, μ.w x * ρ.w y * (if Hits (T.S.E k) c x y then 1 else 0) =
          ∑ y, ∑ x, μ.w x * (ρ.w y * (if Hits (T.S.E k) c x y then 1 else 0)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y hy
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = ∑ x, μ.w x * ∑ y, ρ.w y * (if Hits (T.S.E k) c x y then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
          (fun y => ρ.w y * (if Hits (T.S.E k) c x y then 1 else 0)) (μ.w x)).symm
  have g_eq (x : Fin (T.S.N k)) :
      g x = ∑ y, π.w y * f y * hit (T.S.E k) c x y := by
    have hdeg : deg (T.S.E k) c π.w x = ∑ y, π.w y * hit (T.S.E k) c x y := by
      simp [deg, hit]
    calc
      ∑ y, π.w y * h y * (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x) =
          (∑ y, π.w y * h y * hit (T.S.E k) c x y) -
            (∑ y, π.w y * h y * deg (T.S.E k) c π.w x) := by
        calc
          _ = ∑ y, (π.w y * h y * hit (T.S.E k) c x y -
                π.w y * h y * deg (T.S.E k) c π.w x) := by
            apply Finset.sum_congr rfl
            intro y hy
            ring
          _ = _ := by
            simpa using (Finset.sum_sub_distrib
              (s := (Finset.univ : Finset (Fin (T.S.N k))))
              (fun y => π.w y * h y * hit (T.S.E k) c x y)
              (fun y => π.w y * h y * deg (T.S.E k) c π.w x))
      _ = (∑ y, π.w y * h y * hit (T.S.E k) c x y) - a * deg (T.S.E k) c π.w x := by
        congr 1
        simpa [a] using (Finset.sum_mul (Finset.univ : Finset (Fin (T.S.N k)))
          (fun y => π.w y * h y) (deg (T.S.E k) c π.w x)).symm
      _ = (∑ y, π.w y * h y * hit (T.S.E k) c x y) -
            a * (∑ y, π.w y * hit (T.S.E k) c x y) := by rw [hdeg]
      _ = ∑ y, π.w y * f y * hit (T.S.E k) c x y := by
        calc
          _ = ∑ y, (π.w y * h y * hit (T.S.E k) c x y -
                a * (π.w y * hit (T.S.E k) c x y)) := by
            have hfactor := Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
              (fun y => π.w y * hit (T.S.E k) c x y) a
            rw [hfactor]
            simpa using (Finset.sum_sub_distrib
              (s := (Finset.univ : Finset (Fin (T.S.N k))))
              (fun y => π.w y * h y * hit (T.S.E k) c x y)
              (fun y => a * (π.w y * hit (T.S.E k) c x y))).symm
          _ = ∑ y, π.w y * f y * hit (T.S.E k) c x y := by
            apply Finset.sum_congr rfl
            intro y hy
            simp [f]
            ring
  have tilt_diff (x : Fin (T.S.N k)) :
      (∑ y, rhoPlus.w y * hit (T.S.E k) c x y) -
          ∑ y, rhoMinus.w y * hit (T.S.E k) c x y =
        ∑ y, π.w y * f y * hit (T.S.E k) c x y := by
    calc
      _ = ∑ y, (rhoPlus.w y * hit (T.S.E k) c x y -
          rhoMinus.w y * hit (T.S.E k) c x y) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ y, π.w y * f y * hit (T.S.E k) c x y := by
        apply Finset.sum_congr rfl
        intro y hy
        simp [rhoPlus, rhoMinus, r]
        ring
  have gmean (μ : Law (T.S.N k)) :
      ∑ x, μ.w x * g x =
        dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus := by
    calc
      ∑ x, μ.w x * g x =
          ∑ x, μ.w x * ∑ y, π.w y * f y * hit (T.S.E k) c x y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [g_eq]
      _ = ∑ x, μ.w x *
          ((∑ y, rhoPlus.w y * hit (T.S.E k) c x y) -
            ∑ y, rhoMinus.w y * hit (T.S.E k) c x y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [← tilt_diff]
      _ = dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus := by
        calc
          _ = ∑ x, (μ.w x * (∑ y, rhoPlus.w y * hit (T.S.E k) c x y) -
              μ.w x * (∑ y, rhoMinus.w y * hit (T.S.E k) c x y)) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
          _ = (∑ x, μ.w x * ∑ y, rhoPlus.w y * hit (T.S.E k) c x y) -
                ∑ x, μ.w x * ∑ y, rhoMinus.w y * hit (T.S.E k) c x y := by
            simpa using (Finset.sum_sub_distrib
              (s := (Finset.univ : Finset (Fin (T.S.N k))))
              (fun x => μ.w x * ∑ y, rhoPlus.w y * hit (T.S.E k) c x y)
              (fun x => μ.w x * ∑ y, rhoMinus.w y * hit (T.S.E k) c x y))
          _ = _ := by rw [← dens_eq_row, ← dens_eq_row]
  have has_pos_mass (μ : Law (T.S.N k)) : ∃ x, 0 < μ.w x := by
    by_contra h
    push_neg at h
    have hz : ∀ x, μ.w x = 0 := fun x => le_antisymm (h x) (μ.nonneg x)
    have hs : (∑ x, μ.w x) = 0 := by simp [hz]
    rw [μ.sum_eq_one] at hs
    norm_num at hs
  have cond_supported (S : Finset (Fin (T.S.N k)))
      (hm : 0 < ∑ x ∈ S, τ.w x) : (τ.cond S hm).SupportedIn (T.X k) := by
    intro x hx
    simp [Law.cond, Law.restrict, hτ x hx]
  have cond_width (S : Finset (Fin (T.S.N k)))
      (hm : 0 < ∑ x ∈ S, τ.w x)
      (hmexp : Real.exp (w - W2) < ∑ x ∈ S, τ.w x) :
      (τ.cond S hm).WidthLE W2 := by
    have hlog : w - W2 < Real.log (∑ x ∈ S, τ.w x) := by
      have hlog' := Real.log_lt_log (Real.exp_pos (w - W2)) hmexp
      simpa using hlog'
    have hrestr := Law.WidthLE.restrict hτw hm
    have hcond : (τ.cond S hm).WidthLE (w - Real.log (∑ x ∈ S, τ.w x)) := by
      simpa [Law.cond] using hrestr
    exact Law.WidthLE.mono hcond (by linarith)
  have side_bound (S : Finset (Fin (T.S.N k))) (s : ℝ)
      (hs : s = 1 ∨ s = -1)
      (hmargin : ∀ x ∈ S, 6 * err < s * g x) :
      ∑ x ∈ S, τ.w x ≤ 2 * Real.exp (w - W2) := by
    by_contra hnot
    have hmass : 2 * Real.exp (w - W2) < ∑ x ∈ S, τ.w x := lt_of_not_ge hnot
    have hmexp : Real.exp (w - W2) < ∑ x ∈ S, τ.w x := by
      have he := Real.exp_pos (w - W2)
      linarith
    have hm : 0 < ∑ x ∈ S, τ.w x := lt_trans (Real.exp_pos _) hmexp
    let μ := τ.cond S hm
    have hμs : μ.SupportedIn (T.X k) := by
      simpa [μ] using cond_supported S hm
    have hμw : μ.WidthLE W2 := by
      simpa [μ] using cond_width S hm hmexp
    have hwidthPair :
        (μ.WidthLE wL ∧ rhoPlus.WidthLE wS) ∨
          (μ.WidthLE wS ∧ rhoPlus.WidthLE wL) := by
      rcases hpair with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · exact Or.inl ⟨Law.WidthLE.mono hμw hw2, Law.WidthLE.mono hrhoPlusWidth hw1⟩
      · exact Or.inr ⟨Law.WidthLE.mono hμw hw2, Law.WidthLE.mono hrhoPlusWidth hw1⟩
    have hwidthPairMinus :
        (μ.WidthLE wL ∧ rhoMinus.WidthLE wS) ∨
          (μ.WidthLE wS ∧ rhoMinus.WidthLE wL) := by
      rcases hpair with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
      · exact Or.inl ⟨Law.WidthLE.mono hμw hw2, Law.WidthLE.mono hrhoMinusWidth hw1⟩
      · exact Or.inr ⟨Law.WidthLE.mono hμw hw2, Law.WidthLE.mono hrhoMinusWidth hw1⟩
    have hdiscPlus := hD c μ rhoPlus hμs hrhoPlusSupport hwidthPair
    have hdiscMinus := hD c μ rhoMinus hμs hrhoMinusSupport hwidthPairMinus
    have hμpos := has_pos_mass μ
    have hpoint (x : Fin (T.S.N k)) (hx : 0 < μ.w x) : 6 * err < s * g x := by
      have hxS : x ∈ S := by
        by_contra hnotS
        have hzero : μ.w x = 0 := by simp [μ, Law.cond, Law.restrict, hnotS]
        rw [hzero] at hx
        norm_num at hx
      exact hmargin x hxS
    have hsumlt : ∑ x, μ.w x * (6 * err) < ∑ x, μ.w x * (s * g x) := by
      apply Finset.sum_lt_sum
      · intro x hx
        by_cases hz : μ.w x = 0
        · simp [hz]
        · have hxpos : 0 < μ.w x := lt_of_le_of_ne (μ.nonneg x) (Ne.symm hz)
          exact mul_le_mul_of_nonneg_left (le_of_lt (hpoint x hxpos)) (μ.nonneg x)
      · obtain ⟨x, hx⟩ := hμpos
        exact ⟨x, Finset.mem_univ _, mul_lt_mul_of_pos_left (hpoint x hx) hx⟩
    have hleft : ∑ x, μ.w x * (6 * err) = 6 * err := by
      calc
        ∑ x, μ.w x * (6 * err) = (∑ x, μ.w x) * (6 * err) := by
          simpa using (Finset.sum_mul (Finset.univ : Finset (Fin (T.S.N k)))
            (fun x => μ.w x) (6 * err)).symm
        _ = 6 * err := by rw [μ.sum_eq_one]; ring
    have hright : ∑ x, μ.w x * (s * g x) = s *
        (dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus) := by
      calc
        ∑ x, μ.w x * (s * g x) = s * ∑ x, μ.w x * g x := by
          calc
            ∑ x, μ.w x * (s * g x) = ∑ x, s * (μ.w x * g x) := by
              apply Finset.sum_congr rfl
              intro x hx
              ring
            _ = s * ∑ x, μ.w x * g x := by
              simpa using (Finset.mul_sum (Finset.univ : Finset (Fin (T.S.N k)))
                (fun x => μ.w x * g x) s).symm
        _ = s * (dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus) := by
          rw [gmean]
    have hmean : 6 * err < s *
        (dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus) := by
      rw [hleft] at hsumlt
      rw [hright] at hsumlt
      exact hsumlt
    have herr : 0 ≤ err := le_trans (abs_nonneg _) hdiscPlus
    have hdiff : |dens (T.S.E k) c μ rhoPlus -
        dens (T.S.E k) c μ rhoMinus| ≤ 2 * err := by
      have htri : |(dens (T.S.E k) c μ rhoPlus - 1 / 2) -
          (dens (T.S.E k) c μ rhoMinus - 1 / 2)| ≤
            |dens (T.S.E k) c μ rhoPlus - 1 / 2| +
              |dens (T.S.E k) c μ rhoMinus - 1 / 2| := by
        calc
          |(dens (T.S.E k) c μ rhoPlus - 1 / 2) -
              (dens (T.S.E k) c μ rhoMinus - 1 / 2)| =
            |(dens (T.S.E k) c μ rhoPlus - 1 / 2) +
              -(dens (T.S.E k) c μ rhoMinus - 1 / 2)| := by congr 1 <;> ring
          _ ≤ |dens (T.S.E k) c μ rhoPlus - 1 / 2| +
              |-(dens (T.S.E k) c μ rhoMinus - 1 / 2)| := abs_add_le _ _
          _ = |dens (T.S.E k) c μ rhoPlus - 1 / 2| +
              |dens (T.S.E k) c μ rhoMinus - 1 / 2| := by rw [abs_neg]
      calc
        |dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus| =
            |(dens (T.S.E k) c μ rhoPlus - 1 / 2) -
              (dens (T.S.E k) c μ rhoMinus - 1 / 2)| := by congr 1 <;> ring
        _ ≤ _ := htri
        _ ≤ err + err := add_le_add hdiscPlus hdiscMinus
        _ = 2 * err := by ring
    have hsignbound : s *
        (dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus) ≤
          |dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus| := by
      rcases hs with hs | hs
      · rw [hs]
        simpa using le_abs_self
          (dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus)
      · rw [hs]
        simpa using neg_le_abs
          (dens (T.S.E k) c μ rhoPlus - dens (T.S.E k) c μ rhoMinus)
    linarith
  have hPmargin : ∀ x ∈ P, 6 * err < (1 : ℝ) * g x := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxB, hg⟩
    have hbad : 6 * err < |g x| := (Finset.mem_filter.mp hxB).2
    simpa [abs_of_nonneg hg] using hbad
  have hMmargin : ∀ x ∈ M, 6 * err < (-1 : ℝ) * g x := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxB, hg⟩
    have hbad : 6 * err < |g x| := (Finset.mem_filter.mp hxB).2
    simpa [abs_of_neg hg] using hbad
  have hP := side_bound P 1 (Or.inl rfl) hPmargin
  have hM := side_bound M (-1) (Or.inr rfl) hMmargin
  have hdisjoint : Disjoint P M := by
    apply Finset.disjoint_left.mpr
    intro x hxP hxM
    exact (not_lt_of_ge (Finset.mem_filter.mp hxP).2) (Finset.mem_filter.mp hxM).2
  have hunion : P ∪ M = B := by
    ext x
    simp only [Finset.mem_union, P, M, B, Finset.mem_filter, Finset.mem_univ]
    constructor
    · rintro (⟨hbad, _⟩ | ⟨hbad, _⟩) <;> exact hbad
    · intro hbad
      by_cases hg : 0 ≤ g x
      · exact Or.inl ⟨hbad, hg⟩
      · exact Or.inr ⟨hbad, lt_of_not_ge hg⟩
  calc
    (∑ x ∈ Finset.univ.filter
        (fun x => 6 * err < |∑ y, π.w y * h y *
          (hit (T.S.E k) c x y - deg (T.S.E k) c π.w x)|), τ.w x) =
        ∑ x ∈ B, τ.w x := by simp [B, g]
    _ = (∑ x ∈ P, τ.w x) + ∑ x ∈ M, τ.w x := by
      rw [← hunion]
      exact Finset.sum_union hdisjoint
    _ ≤ 2 * Real.exp (w - W2) + 2 * Real.exp (w - W2) := add_le_add hP hM
    _ = 4 * Real.exp (w - W2) := by ring

/-- SHARED: L12.2, exact heterogeneous centered-moment expansion. -/
theorem centered_moment_identity {N d u : ℕ}
    (τ : Fin N → ℝ) (hτ : ∑ x, τ x = 1)
    (π : Fin d → Fin N → ℝ) (hπ : ∀ l, ∑ y, π l y = 1)
    (φ : Fin d → Fin N → Fin N → ℝ) :
    ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
        ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
      ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
        ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
  classical
  have hcenter (ys : Fin d → Fin N) :
      (∑ x, τ x * ∏ l, φ l x (ys l)) - 1 =
        ∑ x, τ x * ((∏ l, φ l x (ys l)) - 1) := by
    calc
      (∑ x, τ x * ∏ l, φ l x (ys l)) - 1 =
          (∑ x, τ x * ∏ l, φ l x (ys l)) - ∑ x, τ x := by rw [hτ]
      _ = ∑ x, τ x * ((∏ l, φ l x (ys l)) - 1) := by
        calc
          (∑ x, τ x * ∏ l, φ l x (ys l)) - ∑ x, τ x =
              ∑ x, (τ x * ∏ l, φ l x (ys l) - τ x) := by
            rw [← Finset.sum_sub_distrib]
          _ = ∑ x, τ x * ((∏ l, φ l x (ys l)) - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hprod (xs : Fin u → Fin N) (ys : Fin d → Fin N) :
      ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) =
        ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
    calc
      ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) =
          ∏ i ∈ Finset.univ, ((∏ l, φ l (xs i) (ys l)) + (-1 : ℝ)) := by
            apply Finset.prod_congr rfl
            intro i hi
            ring
      _ = ∑ I : Finset (Fin u),
          (∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) *
            ∏ i ∈ Finset.univ \ I, (-1 : ℝ) := by
        simpa using (Finset.prod_add
          (fun i : Fin u => ∏ l, φ l (xs i) (ys l)) (fun _ => (-1 : ℝ))
          (Finset.univ : Finset (Fin u)))
      _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
          ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
        apply Finset.sum_congr rfl
        intro I hI
        have hIsub : I ⊆ (Finset.univ : Finset (Fin u)) := Finset.subset_univ _
        rw [Finset.prod_const, Finset.card_sdiff_of_subset hIsub,
          Finset.card_univ, Fintype.card_fin]
        ring
  have hfactor (xs : Fin u → Fin N) (I : Finset (Fin u)) :
      ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
          ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) =
        ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro ys hys
    calc
      (∏ l, π l (ys l)) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) =
          (∏ l, π l (ys l)) * ∏ l, ∏ i ∈ I, φ l (xs i) (ys l) := by
            congr 1
            exact Finset.prod_comm (s := I) (t := Finset.univ)
              (f := fun i l => φ l (xs i) (ys l))
      _ = ∏ l, (π l (ys l) * ∏ i ∈ I, φ l (xs i) (ys l)) := by
            rw [← Finset.prod_mul_distrib]
  have hpower (ys : Fin d → Fin N) :
      ((∑ x, τ x * ∏ l, φ l x (ys l)) - 1) ^ u =
        ∑ xs : Fin u → Fin N, ∏ i, τ (xs i) * ((∏ l, φ l (xs i) (ys l)) - 1) := by
    rw [hcenter]
    exact Fintype.sum_pow _ _
  calc
    _ = ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
          ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
            ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
      apply Finset.sum_congr rfl
      intro ys hys
      rw [hpower ys]
      congr 1
      apply Finset.sum_congr rfl
      intro xs hxs
      exact Finset.prod_mul_distrib
    _ = ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
          ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
            ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
      calc
        _ = ∑ ys : Fin d → Fin N, ∑ xs : Fin u → Fin N,
              (∏ l, π l (ys l)) *
                ((∏ i, τ (xs i)) *
                  ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) := by
          apply Finset.sum_congr rfl
          intro ys hys
          simpa using (Finset.mul_sum (Finset.univ : Finset (Fin u → Fin N))
            (fun xs => (∏ i, τ (xs i)) *
              ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) (∏ l, π l (ys l)))
        _ = ∑ xs : Fin u → Fin N, ∑ ys : Fin d → Fin N,
              (∏ l, π l (ys l)) *
                ((∏ i, τ (xs i)) *
                  ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) := Finset.sum_comm
        _ = ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
              ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
                ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
          apply Finset.sum_congr rfl
          intro xs hxs
          calc
            ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
                ((∏ i, τ (xs i)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) =
              ∑ ys : Fin d → Fin N, (∏ i, τ (xs i)) *
                ((∏ l, π l (ys l)) * ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) := by
                apply Finset.sum_congr rfl
                intro ys hys
                ring
            _ = (∏ i, τ (xs i)) *
                ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
                  ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1) := by
                simpa using (Finset.mul_sum (Finset.univ : Finset (Fin d → Fin N))
                  (fun ys => (∏ l, π l (ys l)) *
                    ∏ i, ((∏ l, φ l (xs i) (ys l)) - 1)) (∏ i, τ (xs i))).symm
    _ = ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
              ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
      apply Finset.sum_congr rfl
      intro xs hxs
      congr 1
      simp_rw [hprod xs]
      calc
        ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
            ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
              ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) =
          ∑ ys : Fin d → Fin N, ∑ I : Finset (Fin u),
            (∏ l, π l (ys l)) *
              ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) := by
          apply Finset.sum_congr rfl
          intro ys hys
          simpa using (Finset.mul_sum
            (Finset.univ : Finset (Finset (Fin u)))
            (fun I => (-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l))
            (∏ l, π l (ys l)))
        _ = ∑ I : Finset (Fin u), ∑ ys : Fin d → Fin N,
              (∏ l, π l (ys l)) *
                ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) :=
          Finset.sum_comm
        _ = ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
              ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
                ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
          apply Finset.sum_congr rfl
          intro I hI
          calc
            ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
                ((-1 : ℝ) ^ (u - I.card) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) =
              ∑ ys : Fin d → Fin N, (-1 : ℝ) ^ (u - I.card) *
                ((∏ l, π l (ys l)) * ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) := by
                apply Finset.sum_congr rfl
                intro ys hys
                ring
            _ = (-1 : ℝ) ^ (u - I.card) *
                ∑ ys : Fin d → Fin N, (∏ l, π l (ys l)) *
                  ∏ i ∈ I, ∏ l, φ l (xs i) (ys l) := by
                simpa using (Finset.mul_sum (Finset.univ : Finset (Fin d → Fin N))
                  (fun ys => (∏ l, π l (ys l)) *
                    ∏ i ∈ I, ∏ l, φ l (xs i) (ys l)) ((-1 : ℝ) ^ (u - I.card))).symm
    _ = ∑ xs : Fin u → Fin N, (∏ i, τ (xs i)) *
          ∑ I : Finset (Fin u), (-1 : ℝ) ^ (u - I.card) *
            ∏ l, ∑ y, π l y * ∏ i ∈ I, φ l (xs i) y := by
      apply Finset.sum_congr rfl
      intro xs hxs
      congr 1
      apply Finset.sum_congr rfl
      intro I hI
      rw [← hfactor xs I]

/-- SHARED: L12.3a, one-free-coordinate gated interaction tail. -/
theorem inter_tail_one (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (u : ℕ) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)) (l : Fin S.d)
      (J : Finset (Fin u)) (i0 : Fin u), i0 ∈ J → 2 ≤ J.card →
      ∀ xs : Fin u → Fin (T.S.N k),
        (∀ i ∈ J, i ≠ i0 →
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) (xs i)) →
        ∑ z ∈ Finset.univ.filter (fun z =>
          DegGate (T.S.E k) c (S.π l).w C0 (bstar T k) z ∧
            100 * 3 ^ u * C0 * bstar T k <
              |inter (T.S.E k) c (S.π l).w J (Function.update xs i0 z)|), S.τ.w z ≤
          Real.exp (-(κ.α * T.S.n k / 3)) := by
  sorry

/-- SHARED: L12.4, the moderate interaction moment bound. -/
theorem moderate_moment (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop, ∀ (S : InterSetting T k (κ.xs / 4)), S.DegOK c C0 →
      |∑ xs : Fin κ.u → Fin (T.S.N k),
          if Moderate (T.S.E k) c (fun l => (S.π l).w) (2 * κ.ξ) xs
          then prodW S.τ.w xs * Phi (T.S.E k) c (fun l => (S.π l).w) xs else 0| ≤
        (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) := by
  sorry

/-- SHARED: L12.5(iv), homogeneous extension peeling and the lower-tail estimate. -/
theorem homogeneous_lower_tail (κ : CConsts) (hκ : κ.Admissible) (T : Stage)
    (hDeep : DeepDisc T κ.xs κ.α 0.04) (c : Colour) (C0 : ℝ) (hC0 : 1 ≤ C0) :
    ∀ᶠ k in atTop, ∀ d ≤ T.S.n k, ∀ (τ π : Law (T.S.N k)) (Sp : Finset (Fin (T.S.N k)))
      (Q : ℝ) (t : ℝ), 0 ≤ t → t < 1 →
      (∀ x ∈ Sp, DegGate (T.S.E k) c π.w C0 (bstar T k) x) →
      (∑ ys : Fin d → Fin (T.S.N k),
        if Zmass (T.S.E k) c τ.w (fun _ => π.w) ys < t then ∏ l, π.w (ys l) else 0) ≤
        (1 - t) ^ (-(κ.u : ℝ)) * (T.S.n k : ℝ) ^ (-(3 * κ.R : ℝ)) := by
  sorry

end HypercubeRamsey.S15.Needs
