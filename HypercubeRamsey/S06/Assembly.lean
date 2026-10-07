import HypercubeRamsey.S06.EvenRows
import HypercubeRamsey.S03.NearProductInjection
import HypercubeRamsey.Framework.Hall

/-!
# Section 6 assembly and the one-shot export

L6.1 (06:4–12, 06:14–887).  The export is assembled from the reduction (L6.1a), the geometry (L6.1b), the states
(L6.1e) and the staged construction (L6.1c–n): Steps 1–3, the conditioning stages, the centre stage, the odd rows
and loads, the odd injection (Lemma 3.9) and the even reconstruction.  The total exceptional mass through the
stagewise laws is below one, so a common successful outcome exists (06:882–884); its odd labels and even rows are
Hall data (06:884–885).  No step of this file has a proof hole of its own.
-/

namespace HypercubeRamsey
namespace S06

open OAI.HypercubeRamsey
open Classical
open scoped BigOperators

noncomputable section

/-- The final Hall data: an injective odd placement and fractional even rows (06:884–885). -/
structure FractionalRows6 (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) where
  oddMap : OddRole6 n → Fin N
  oddInjective : Function.Injective oddMap
  evenRows : EvenRole6 n → Fin N → ℝ
  evenNonneg : ∀ a x, 0 ≤ evenRows a x
  evenMass : ∀ a, ∑ x, evenRows a x = 1
  evenSupport : ∀ a x, evenRows a x ≠ 0 →
    ∀ b : OddRole6 n, (cube n).Adj a.1 b.1 → Hits E G x (oddMap b)
  columnLoad : ∀ x, ∑ a, evenRows a x ≤ 1

/-- L6.1n and F-HallEmbed: the fractional rows give a monochromatic cube in colour `G`. -/
theorem L6_1n {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour}
    (R : FractionalRows6 n N E G) : CubeAt n N E := by
  classical
  let support : EvenRole6 n → Finset (Fin N) := fun a =>
    Finset.univ.filter fun x => R.evenRows a x ≠ 0
  obtain ⟨evenMap, evenInjective, evenSupport⟩ :=
    exists_injective_of_fractional R.evenRows support R.evenNonneg R.evenMass
      (by
        intro a x hx
        by_contra hne
        apply hx
        simp [support, hne])
      R.columnLoad
  refine ⟨G, cube_copy_of_parts evenMap R.oddMap evenInjective R.oddInjective ?_⟩
  intro a b hab
  have hmem := evenSupport a
  simp [support] at hmem
  have hne : R.evenRows a (evenMap a) ≠ 0 := hmem
  exact R.evenSupport a (evenMap a) hne b hab

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

namespace Ctx6

/-- Odd row atoms are at most `N^{−.95}` on good odd outcomes (06:763). -/
def RowAtoms : Prop :=
  ∀ H C (u : CubeVertex n) y, X.histLaw.w H ≠ 0 → X.OddGood H C → ¬ IsEvenRole u →
    X.oddRow H C u y ≤ (N : ℝ) ^ (-(0.95 : ℝ))

/-- The final success event (06:882–885). -/
def AllGood (ω : X.Hist × (X.Centre × (OddRole6 n → Fin N))) : Prop :=
  X.OddGood ω.1 ω.2.1 ∧ Function.Injective ω.2.2 ∧
    (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
      ∀ a, ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a ≤ 1

end Ctx6

/-- L6.1m (atoms, 06:763): `e^{m^{.15}}/N` and `n^{.05J}/N` are at most `N^{−.95}` once `N ≥ 2^n` and `n` is large. -/
theorem L6_1m_atoms (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X => X.OddRowBounds → X.RowAtoms := by
  refine ⟨10000000000, 1, ?_⟩
  intro n N E G M X hL hRows H C u y hH hGood hu
  have hnBig : 10000000000 ≤ n := hL.1
  have hnOne : 1 ≤ n := by omega
  have hnTenK : 10000 ≤ n := by omega
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hnOne)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
  have hNlower : (2 : ℝ) ^ n ≤ (N : ℝ) := by simpa using hL.2.1
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < 2 ^ n) hNlower
  have hAlpha : α₆ p₀ ≤ 1 :=
    (height_exponents6_admissible p₀ hadm.2.2.1).2.2.1.trans (by norm_num)
  have hpowAlpha : (n : ℝ) ^ α₆ p₀ ≤ n :=
    by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnreal hAlpha
  have hmle : X.m ≤ n := by
    change X.g.L.m ≤ n
    rw [X.g.m_eq]
    exact Nat.ceil_le.mpr hpowAlpha
  have hmcast : (X.m : ℝ) ≤ n := by exact_mod_cast hmle
  have hJpow : (X.J : ℝ) ≤ (n : ℝ) ^ (1 / 25 : ℝ) := by
    change (Nat.floor ((X.m : ℝ) ^ (1 / 25 : ℝ)) : ℝ) ≤ _
    calc
      (Nat.floor ((X.m : ℝ) ^ (1 / 25 : ℝ)) : ℝ) ≤ (X.m : ℝ) ^ (1 / 25 : ℝ) :=
        Nat.floor_le (by positivity)
      _ ≤ (n : ℝ) ^ (1 / 25 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) hmcast
        norm_num
  have hlog10 : 10 * Real.log 10 ≤ Real.log (n : ℝ) := by
    have hpow : (10 : ℝ) ^ 10 ≤ n := by exact_mod_cast hnBig
    calc
      10 * Real.log 10 = Real.log ((10 : ℝ) ^ 10) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) hpow
  have hlog10' : Real.log 10 ≤ (1 / 10 : ℝ) * Real.log (n : ℝ) := by nlinarith
  have hten : (10 : ℝ) ≤ (n : ℝ) ^ (1 / 10 : ℝ) := by
    rw [Real.le_rpow_iff_log_le (by norm_num) hnPos]
    exact hlog10'
  have hpow23 : (10 : ℝ) ≤ (n : ℝ) ^ (23 / 50 : ℝ) :=
    hten.trans (Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num))
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 100 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hnrealTen : (10000 : ℝ) ≤ n := by exact_mod_cast hnTenK
    have hprod : 0 ≤ ((n : ℝ) - 10000) * n :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith
  have hlowLog : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ (1 / 100 : ℝ) * n := by
    have hmpow : (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ (n : ℝ) ^ (15 / 100 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hmcast (by norm_num)
    have hnPow : (n : ℝ) ^ (15 / 100 : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnreal (by norm_num)
    have hsqrt' : (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (n : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    calc
      (X.m : ℝ) ^ (15 / 100 : ℝ) ≤ (n : ℝ) ^ (15 / 100 : ℝ) := hmpow
      _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) := hnPow
      _ = Real.sqrt (n : ℝ) := hsqrt'
      _ ≤ (1 / 100 : ℝ) * n := by linarith [hsqrt]
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have h := Real.log_le_rpow_div (x := (n : ℝ)) (by positivity)
      (by norm_num : (0 : ℝ) < 1 / 2)
    simpa [Real.sqrt_eq_rpow, mul_comm] using h
  have hprodPow : (n : ℝ) ^ (27 / 50 : ℝ) * (n : ℝ) ^ (23 / 50 : ℝ) = n := by
    rw [← Real.rpow_add hnPos]
    norm_num
  have hpow54 : 10 * (n : ℝ) ^ (27 / 50 : ℝ) ≤ n := by
    have hmul := mul_le_mul_of_nonneg_left hpow23
      (Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity) (27 / 50 : ℝ))
    nlinarith [hprodPow]
  have hterm : (1 / 20 : ℝ) * (X.J : ℝ) * Real.log (n : ℝ) ≤ (1 / 100 : ℝ) * n := by
    calc
      (1 / 20 : ℝ) * (X.J : ℝ) * Real.log (n : ℝ) ≤
          (1 / 20 : ℝ) * (n : ℝ) ^ (1 / 25 : ℝ) * Real.log (n : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hJpow (by norm_num)
        · exact Real.log_nonneg (by exact_mod_cast hnOne)
      _ ≤ (1 / 20 : ℝ) * (n : ℝ) ^ (1 / 25 : ℝ) * (2 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = (1 / 10 : ℝ) * ((n : ℝ) ^ (1 / 25 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        ring
      _ = (1 / 10 : ℝ) * (n : ℝ) ^ ((1 / 25 : ℝ) + (1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hnPos]
      _ = (1 / 10 : ℝ) * (n : ℝ) ^ (27 / 50 : ℝ) := by
        congr 2
        norm_num
      _ ≤ (1 / 100 : ℝ) * n := by nlinarith [hpow54]
  have hlowExp : Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ)) ≤ Real.exp ((1 / 100 : ℝ) * n) :=
    Real.exp_le_exp.mpr hlowLog
  have hhighExp : (n : ℝ) ^ ((5 / 100 : ℝ) * (X.J : ℝ)) ≤ Real.exp ((1 / 100 : ℝ) * n) := by
    rw [Real.rpow_def_of_pos hnPos]
    apply Real.exp_le_exp.mpr
    nlinarith [hterm]
  have hbaseExp : Real.exp (1 / 40 : ℝ) ≤ (2 : ℝ) ^ (5 / 100 : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.log_two_gt_d9]
  have hExpGrow : Real.exp ((1 / 100 : ℝ) * n) ≤ Real.exp (1 / 40 : ℝ) ^ n := by
    calc
      Real.exp ((1 / 100 : ℝ) * n) ≤ Real.exp ((1 / 40 : ℝ) * n) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp (1 / 40 : ℝ) ^ n := by
        simpa [mul_comm] using (Real.exp_nat_mul (1 / 40 : ℝ) n)
  have hpowGrow : Real.exp (1 / 40 : ℝ) ^ n ≤ ((2 : ℝ) ^ (5 / 100 : ℝ)) ^ n :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hbaseExp n
  have hNpow : ((2 : ℝ) ^ n) ^ (5 / 100 : ℝ) ≤ (N : ℝ) ^ (5 / 100 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hNlower (by norm_num)
  have hNexp : Real.exp ((1 / 100 : ℝ) * n) ≤ (N : ℝ) ^ (5 / 100 : ℝ) := by
    calc
      Real.exp ((1 / 100 : ℝ) * n) ≤ Real.exp (1 / 40 : ℝ) ^ n := hExpGrow
      _ ≤ ((2 : ℝ) ^ (5 / 100 : ℝ)) ^ n := hpowGrow
      _ = ((2 : ℝ) ^ n) ^ (5 / 100 : ℝ) := Real.rpow_pow_comm (by norm_num) _ _
      _ ≤ (N : ℝ) ^ (5 / 100 : ℝ) := hNpow
  have hvalid : X.OddValid H C X.Rlong (X.g.L.stateOf u) := hGood.2.1 u hu
  obtain ⟨_, _, hcap, _, _⟩ := hRows H C u hH hu hvalid
  have hcapY := hcap y
  have hcapFinal : (N : ℝ) * X.oddRow H C u y ≤ (N : ℝ) ^ (5 / 100 : ℝ) := by
    by_cases hmode : X.stMode (X.g.L.stateOf u) = .low
    · rw [if_pos hmode] at hcapY
      exact hcapY.trans (hlowExp.trans hNexp)
    · rw [if_neg hmode] at hcapY
      exact hcapY.trans (hhighExp.trans hNexp)
  have hrowRpow : (N : ℝ) ^ (5 / 100 : ℝ) =
      (N : ℝ) ^ (-(0.95 : ℝ)) * (N : ℝ) := by
    calc
      (N : ℝ) ^ (5 / 100 : ℝ) = (N : ℝ) ^ (-(0.95 : ℝ) + 1) := by congr 1 <;> norm_num
      _ = (N : ℝ) ^ (-(0.95 : ℝ)) * (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_add hNpos _ _
      _ = (N : ℝ) ^ (-(0.95 : ℝ)) * (N : ℝ) := by rw [Real.rpow_one]
  have hcancel : (N : ℝ) * X.oddRow H C u y ≤
      (N : ℝ) * (N : ℝ) ^ (-(0.95 : ℝ)) := by
    calc
      (N : ℝ) * X.oddRow H C u y ≤ (N : ℝ) ^ (-(0.95 : ℝ)) * (N : ℝ) := by
        simpa only [hrowRpow] using hcapFinal
      _ = (N : ℝ) * (N : ℝ) ^ (-(0.95 : ℝ)) := by ring
  exact le_of_mul_le_mul_left hcancel hNpos

/-- Lemma 3.9 supplies the odd injection laws at every good entering outcome (06:761–766). -/
theorem injection_family6 (γ p₀ K : ℝ) :
    ForLarge6 γ p₀ K fun n N _ _ _ X =>
      X.OddRowBounds → X.RowAtoms → ∃ Jf : X.Hist → X.Centre → FinProb (OddRole6 n → Fin N), X.JfOK Jf := by
  obtain ⟨d₀, hd₀⟩ := near_product_injection
  refine ⟨0, (d₀ : ℝ) + 1, fun n N E G M X hL hO hA => ?_⟩
  have hN : d₀ ≤ N := by
    have h1 : ((d₀ : ℝ) + 1) * 2 ^ n ≤ N := hL.2.1
    have h2 : (d₀ : ℝ) + 1 ≤ ((d₀ : ℝ) + 1) * 2 ^ n :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    exact_mod_cast (by linarith : (d₀ : ℝ) ≤ N)
  have key : ∀ H C, X.histLaw.w H ≠ 0 → X.OddGood H C →
      ∃ J : FinProb (OddRole6 n → Fin N),
        (∀ ω, J.w ω ≠ 0 → Function.Injective ω) ∧
        (∀ (u : OddRole6 n) y, J.pr (fun ω => ω u = y) = X.oddRow H C u.1 y) ∧
        ∀ (S : Finset (OddRole6 n)) (o : OddRole6 n → Fin N), (S.card : ℝ) ≤ (N : ℝ) ^ (0.025 : ℝ) →
          J.pr (fun ω => ∀ u ∈ S, ω u = o u) ≤
            Real.exp ((N : ℝ) ^ (-(0.04 : ℝ)) * S.card) * ∏ u ∈ S, X.oddRow H C u.1 (o u) := by
    intro H C hH hG
    have hrow := fun u : OddRole6 n => hO H C u.1 hH u.2 (hG.2.1 u.1 u.2)
    let p : OddRole6 n → FinProb (Fin N) := fun u =>
      { w := X.oddRow H C u.1
        nonneg := (hrow u).1
        sum_eq_one := (hrow u).2.1 }
    have hlab : ∀ u y, labMarg (p u) id y = X.oddRow H C u.1 y := by
      intro u y
      unfold labMarg
      simp [p]
    have hcap : ∀ u y, labMarg (p u) id y ≤ (N : ℝ) ^ (-(0.95 : ℝ)) := by
      intro u y
      rw [hlab]
      exact hA H C u.1 y hH hG u.2
    have hcol : ∀ y, ∑ u, labMarg (p u) id y ≤ 0.4 := by
      intro y
      simp_rw [hlab]
      have hsub : ∑ u : OddRole6 n, X.oddRow H C u.1 y = ∑ u ∈ X.oddRoles, X.oddRow H C u y :=
        (Finset.sum_subtype X.oddRoles (fun x => by simp [Ctx6.oddRoles]) (fun u => X.oddRow H C u y)).symm
      rw [hsub]
      have := hG.2.2 y
      linarith
    obtain ⟨J, hinj, hmarg, hjoint⟩ := hd₀ N hN (fun _ => id) p hcap hcol
    refine ⟨J, fun ω hω => hinj ω hω, fun u y => hmarg u y, fun S o hS => hjoint S o hS⟩
  refine ⟨fun H C => if h : X.histLaw.w H ≠ 0 ∧ X.OddGood H C then Classical.choose (key H C h.1 h.2)
    else pointMass6 (fun _ => X.y₀), ?_⟩
  intro H C hH hG
  simp only [dif_pos (And.intro hH hG)]
  exact Classical.choose_spec (key H C hH hG)

/-- At a supported successful outcome the odd labels and even rows are Hall data (06:884–885). -/
theorem fractionalRows_of_good6 (hDen : X.EvenDensity) (Jf : X.Hist → X.Centre → FinProb (OddRole6 n → Fin N))
    (ω : X.Hist × (X.Centre × (OddRole6 n → Fin N))) (hω : (X.fullLaw Jf).w ω ≠ 0) (hg : X.AllGood ω) :
    Nonempty (FractionalRows6 n N E G) := by
  have hH : X.histLaw.w ω.1 ≠ 0 := (bind_w_ne_zero6 _ _ ω hω).1
  have hd := fun a : EvenRole6 n => hDen ω.1 ω.2.1 a.1 ω.2.2 hH a.2 (hg.2.2.1 a.1 a.2)
  refine ⟨{
    oddMap := ω.2.2
    oddInjective := hg.2.1
    evenRows := fun a x => X.evenRow ω.1 ω.2.1 a.1 ω.2.2 x
    evenNonneg := fun a x => (hd a).1 x
    evenMass := fun a => (hd a).2.1
    evenSupport := fun a x hx b hab => (hd a).2.2.1 x hx b (by simp [Ctx6.oddNbrs, hab])
    columnLoad := fun x => ?_ }⟩
  have hsub : ∑ a : EvenRole6 n, X.evenRow ω.1 ω.2.1 a.1 ω.2.2 x =
      ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 x :=
    (Finset.sum_subtype X.evenRoles (fun v => by simp [Ctx6.evenRoles])
      (fun v => X.evenRow ω.1 ω.2.1 v ω.2.2 x)).symm
  rw [hsub]
  exact hg.2.2.2 x

/-- The union of all exceptional events through the stagewise laws has probability at most `1/2`
(06:882–884). -/
theorem final_union6 (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun _ _ _ _ _ X =>
      X.StepFacts → X.StageFacts → X.CentreFacts → X.OddRowFacts → X.LoadFacts → X.EvenFacts →
        ∀ Jf, X.JfOK Jf → (X.fullLaw Jf).pr (fun ω => ¬ X.AllGood ω) ≤ 1 / 2 := by
  have hK : 0 < K := hadm.2.2.2
  have hCkc : 0 < Ckc K := by unfold Ckc Ckh Ckb; positivity
  refine ⟨0, 10 * Ckc K, fun n N E G M X hL _hS hT hC _hO hLd hE Jf hJ => ?_⟩
  obtain ⟨hV0, _hCo, _hHi, _hSu⟩ := hT
  obtain ⟨_hCB, _hMB, _hED, _hHB, _hVD, hUn⟩ := hC
  obtain ⟨hOB, hOH, hOC, hEB, hEH, _hOJ⟩ := hLd
  obtain ⟨hGate, _hDom, hTest, _hDen, _hMean, hLoad, _hSel, _hJoint⟩ := hE
  -- the stage 1 support consists of retained parents
  have hV0pos : 0 < X.initLaw.pr X.V0Good := by
    have : (1 / 2 : ℝ) ≤ X.initLaw.pr X.V0Good := hV0
    linarith
  have hst1 : ∀ v, X.stage1Law.w v ≠ 0 → X.V0Good v := fun v hv => (restrictOr6_supp hV0pos hv).1
  -- two-stage history bounds
  have hist2 : ∀ (A : X.Base → Prop) (B : X.Hist → Prop),
      (∀ v, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).pr (fun c => A (v, c)) ≤ 1 / 100) →
      (∀ v c, X.stage1Law.w v ≠ 0 → X.V0Good v → (X.stage2Law v).w c ≠ 0 → ¬ A (v, c) →
        (X.stage3Law (v, c)).pr (fun Z => B ((v, c), Z)) ≤ 1 / 100) →
      X.histLaw.pr B ≤ 2 / 100 := by
    intro A B hA hB
    have h12 : (FinProb.bind X.stage1Law X.stage2Law).pr A ≤ 1 / 100 := by
      have h := pr_bind_le6 X.stage1Law X.stage2Law A (fun _ => False) (1 / 100)
        (fun v hv _ => hA v hv (hst1 v hv)) (by norm_num)
      have h0 : X.stage1Law.pr (fun _ => False) = 0 := pr_zero_of_supp6 _ (fun _ _ h => h)
      linarith
    have h := pr_bind_le6 (FinProb.bind X.stage1Law X.stage2Law) X.stage3Law B A (1 / 100)
      (fun b₀ hb₀ hnA => hB b₀.1 b₀.2 (bind_w_ne_zero6 _ _ b₀ hb₀).1 (hst1 _ (bind_w_ne_zero6 _ _ b₀ hb₀).1)
        (bind_w_ne_zero6 _ _ b₀ hb₀).2 hnA) (by norm_num)
    have heq : X.histLaw = FinProb.bind (FinProb.bind X.stage1Law X.stage2Law) X.stage3Law := rfl
    rw [heq]
    linarith
  have hLong : X.histLaw.pr (fun H => ∃ y, Ckh K < X.longAvg H y) ≤ 2 / 100 :=
    hist2 (fun b₀ => ∃ y, Ckb K < X.baseAvg b₀ y) _ (fun v hv1 hv => hOB v hv1 hv)
      (fun v c hv1 hv hc hnA => hOH v c hv1 hv hc (by push_neg at hnA; exact hnA))
  have hMix : X.histLaw.pr (fun H => ∃ a, Clh K < X.mixAvg H a) ≤ 2 / 100 :=
    hist2 (fun b₀ => ∃ a, Clb K < X.phiAvg b₀ a) _ (fun v hv1 hv => hEB v hv1 hv)
      (fun v c hv1 hv hc hnA => hEH v c hv1 hv hc (by push_neg at hnA; exact hnA))
  -- odd column sums from the normalized average
  have hNbig : 10 * Ckc K * 2 ^ n ≤ (N : ℝ) := hL.2.1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNbig
  have hcol : ∀ H C, (∀ y, X.rowAvg H C y ≤ Ckc K) → ∀ y, ∑ u ∈ X.oddRoles, X.oddRow H C u y ≤ 1 / 10 := by
    intro H C hr y
    have hrow := hr y
    unfold Ctx6.rowAvg at hrow
    rw [← Finset.mul_sum] at hrow
    have hcard : ((X.oddRoles.card : ℕ) : ℝ) ≤ 2 ^ n := by
      have h1 : X.oddRoles.card ≤ Fintype.card (CubeVertex n) := Finset.card_le_univ _
      have h2 : Fintype.card (CubeVertex n) = 2 ^ n := by simp
      exact_mod_cast h2 ▸ h1
    rcases Nat.eq_zero_or_pos X.oddRoles.card with h0 | hpos
    · have he : X.oddRoles = ∅ := Finset.card_eq_zero.mp h0
      rw [he, Finset.sum_empty]
      norm_num
    · have hc : (0 : ℝ) < X.oddRoles.card := by exact_mod_cast hpos
      have h1 : (N : ℝ) * ∑ u ∈ X.oddRoles, X.oddRow H C u y ≤ X.oddRoles.card * Ckc K :=
        (inv_mul_le_iff₀ hc).1 hrow
      have h2 : (N : ℝ) * ∑ u ∈ X.oddRoles, X.oddRow H C u y ≤ 2 ^ n * Ckc K :=
        le_trans h1 (mul_le_mul_of_nonneg_right hcard hCkc.le)
      by_contra hcon
      push_neg at hcon
      have h3 := mul_lt_mul_of_pos_left hcon hNpos
      nlinarith
  -- the centre stage at good histories
  have hodd : ∀ H, X.histLaw.w H ≠ 0 → (∀ y, X.longAvg H y ≤ Ckh K) →
      (X.centreLaw H).pr (fun C => ¬ X.OddGood H C) ≤ 2 / 100 := by
    intro H hH hlong
    have h1 := hUn H hH
    have h2 := hOC H hH hlong
    have hsub := pr_mono6 (X.centreLaw H)
      (A := fun C => ¬ X.OddGood H C)
      (B := fun C => ¬ (X.GeoGood H C ∧ X.AllOddValid H C) ∨ (X.AllOddValid H C ∧ ∃ y, Ckc K < X.rowAvg H C y))
      (by
        intro C hC
        by_contra hcon
        push_neg at hcon
        obtain ⟨hgv, hrow⟩ := hcon
        exact hC ⟨hgv.1, hgv.2, hcol H C (hrow hgv.2)⟩)
    have hor := pr_or_le6 (X.centreLaw H) (fun C => ¬ (X.GeoGood H C ∧ X.AllOddValid H C))
      (fun C => X.AllOddValid H C ∧ ∃ y, Ckc K < X.rowAvg H C y)
    linarith
  -- the five exceptional events
  have hE0 : (X.fullLaw Jf).pr (fun ω => ¬ X.OddGood ω.1 ω.2.1) ≤ 4 / 100 := by
    have h := pr_bind_le6 X.histLaw (fun H => (X.centreLaw H).bind (Jf H)) (fun ω => ¬ X.OddGood ω.1 ω.2.1)
      (fun H => ∃ y, Ckh K < X.longAvg H y) (2 / 100)
      (fun H hH hnA => (pr_bind_fst6 (X.centreLaw H) (Jf H) (fun C => ¬ X.OddGood H C)).le.trans
        (hodd H hH (by push_neg at hnA; exact hnA))) (by norm_num)
    have heq : X.fullLaw Jf = X.histLaw.bind (fun H => (X.centreLaw H).bind (Jf H)) := rfl
    rw [heq]
    linarith
  have hE1 : (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧ ¬ Function.Injective ω.2.2) = 0 := by
    apply pr_zero_of_supp6
    intro ω hω hbad
    obtain ⟨hH, hK'⟩ := bind_w_ne_zero6 X.histLaw (fun H => (X.centreLaw H).bind (Jf H)) ω hω
    obtain ⟨_, hy⟩ := bind_w_ne_zero6 (X.centreLaw ω.1) (Jf ω.1) ω.2 hK'
    exact hbad.2 ((hJ ω.1 ω.2.1 hH hbad.1).1 ω.2.2 hy)
  have hE2 : (X.fullLaw Jf).pr (fun ω => X.OddGood ω.1 ω.2.1 ∧
      ∃ v : CubeVertex n, IsEvenRole v ∧ ¬ X.EvenValid ω.1 ω.2.1 v ω.2.2) ≤ 1 / 100 := by
    refine le_trans (pr_mono_supp6 _ ?_) (hTest Jf hJ)
    intro ω hω hbad
    obtain ⟨hG, v, hv, hnv⟩ := hbad
    have hH := (bind_w_ne_zero6 X.histLaw (fun H => (X.centreLaw H).bind (Jf H)) ω hω).1
    exact ⟨hG, v, hv, fun hmc => hnv ⟨hGate ω.1 ω.2.1 v hH hG hv, hmc⟩⟩
  have hE3 := hLoad Jf hJ
  have hE4 : (X.fullLaw Jf).pr (fun ω => ∃ a, Clh K < X.mixAvg ω.1 a) ≤ 2 / 100 :=
    (pr_bind_fst6 X.histLaw (fun H => (X.centreLaw H).bind (Jf H)) (fun H => ∃ a, Clh K < X.mixAvg H a)).le.trans
      hMix
  -- every failure is one of them
  have hcover := pr_mono6 (X.fullLaw Jf) (A := fun ω => ¬ X.AllGood ω)
    (B := fun ω => ¬ X.OddGood ω.1 ω.2.1 ∨ ((X.OddGood ω.1 ω.2.1 ∧ ¬ Function.Injective ω.2.2) ∨
      ((X.OddGood ω.1 ω.2.1 ∧ ∃ v : CubeVertex n, IsEvenRole v ∧ ¬ X.EvenValid ω.1 ω.2.1 v ω.2.2) ∨
        ((X.OddGood ω.1 ω.2.1 ∧ (∀ a, X.mixAvg ω.1 a ≤ Clh K) ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a) ∨
          (∃ a, Clh K < X.mixAvg ω.1 a)))))
    (by
      intro ω hng
      by_cases hG : X.OddGood ω.1 ω.2.1
      · right
        by_cases hinj : Function.Injective ω.2.2
        · right
          by_cases hval : ∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2
          · right
            by_cases hmix : ∀ a, X.mixAvg ω.1 a ≤ Clh K
            · left
              refine ⟨hG, hmix, hval, ?_⟩
              by_contra hcol'
              push_neg at hcol'
              exact hng ⟨hG, hinj, hval, hcol'⟩
            · right
              push_neg at hmix
              exact hmix
          · left
            push_neg at hval
            exact ⟨hG, hval⟩
        · left
          exact ⟨hG, hinj⟩
      · left
        exact hG)
  have hu1 := pr_or_le6 (X.fullLaw Jf) (fun ω => ¬ X.OddGood ω.1 ω.2.1)
    (fun ω => (X.OddGood ω.1 ω.2.1 ∧ ¬ Function.Injective ω.2.2) ∨
      ((X.OddGood ω.1 ω.2.1 ∧ ∃ v : CubeVertex n, IsEvenRole v ∧ ¬ X.EvenValid ω.1 ω.2.1 v ω.2.2) ∨
        ((X.OddGood ω.1 ω.2.1 ∧ (∀ a, X.mixAvg ω.1 a ≤ Clh K) ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a) ∨
          (∃ a, Clh K < X.mixAvg ω.1 a))))
  have hu2 := pr_or_le6 (X.fullLaw Jf) (fun ω => X.OddGood ω.1 ω.2.1 ∧ ¬ Function.Injective ω.2.2)
    (fun ω => (X.OddGood ω.1 ω.2.1 ∧ ∃ v : CubeVertex n, IsEvenRole v ∧ ¬ X.EvenValid ω.1 ω.2.1 v ω.2.2) ∨
        ((X.OddGood ω.1 ω.2.1 ∧ (∀ a, X.mixAvg ω.1 a ≤ Clh K) ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a) ∨
          (∃ a, Clh K < X.mixAvg ω.1 a)))
  have hu3 := pr_or_le6 (X.fullLaw Jf)
    (fun ω => X.OddGood ω.1 ω.2.1 ∧ ∃ v : CubeVertex n, IsEvenRole v ∧ ¬ X.EvenValid ω.1 ω.2.1 v ω.2.2)
    (fun ω => (X.OddGood ω.1 ω.2.1 ∧ (∀ a, X.mixAvg ω.1 a ≤ Clh K) ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a) ∨
          (∃ a, Clh K < X.mixAvg ω.1 a))
  have hu4 := pr_or_le6 (X.fullLaw Jf)
    (fun ω => X.OddGood ω.1 ω.2.1 ∧ (∀ a, X.mixAvg ω.1 a ≤ Clh K) ∧
          (∀ v : CubeVertex n, IsEvenRole v → X.EvenValid ω.1 ω.2.1 v ω.2.2) ∧
            ∃ a, 1 < ∑ v ∈ X.evenRoles, X.evenRow ω.1 ω.2.1 v ω.2.2 a)
    (fun ω => ∃ a, Clh K < X.mixAvg ω.1 a)
  linarith

/-- The staged construction gives a `G`-cube in every Section 6 context of large dimension. -/
theorem section6_main (γ p₀ K : ℝ) (hadm : Admissible6 γ p₀ K) :
    ForLarge6 γ p₀ K fun n N E _ _ _ => CubeAt n N E := by
  have h := (stepFacts6 γ p₀ K hadm).and <| (stageFacts6 γ p₀ K hadm).and <| (centreFacts6 γ p₀ K hadm).and <|
    (oddRowFacts6 γ p₀ K hadm).and <| (loadFacts6 γ p₀ K hadm).and <| (evenFacts6 γ p₀ K hadm).and <|
    (L6_1m_atoms γ p₀ K hadm).and <| (injection_family6 γ p₀ K).and (final_union6 γ p₀ K hadm)
  refine h.mono ?_
  intro n N E G M X ⟨hS, hT, hC, hO, hL, hE, hA, hJ, hU⟩
  have hT' := hT hS
  have hC' := hC hS hT'
  have hO' := hO hS hT' hC'
  have hL' := hL hS hT' hO'
  have hE' := hE hS hT' hC' hO'
  obtain ⟨Jf, hJf⟩ := hJ hO'.2.1 (hA hO'.2.1)
  have hbound := hU hS hT' hC' hO' hL' hE' Jf hJf
  obtain ⟨ω, hω, hg⟩ := exists_of_pr_lt_one6 (X.fullLaw Jf) X.AllGood (by linarith)
  obtain ⟨R⟩ := fractionalRows_of_good6 X hE'.2.2.2.1 Jf ω hω hg
  exact L6_1n R

/-- L6.1 (one-shot form), with the frozen binders and hypotheses from scratch-B. -/
theorem small_polynomial_broad_side_core :
    ∃ Dstar > (0 : ℝ), ∀ γ p₀ K : ℝ, 0 < γ → γ < 1 → 0 < p₀ → 0 < K →
      ∃ (n₀ : ℕ) (C₀ : ℝ),
        ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
          LargeAt n₀ C₀ n N → M.Balanced K →
          (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
          (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar)) →
          (∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y →
            1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y) →
          CubeAt n N E := by
  refine ⟨Dstar₆, by norm_num [Dstar₆], ?_⟩
  intro γ p₀ K hγ0 hγ1 hp hK
  have hadm : Admissible6 γ p₀ K := ⟨hγ0, hγ1, hp, hK⟩
  have hα0 : 0 < α₆ p₀ := lt_min (by norm_num) (by linarith)
  have hα1 : α₆ p₀ ≤ 1 / 100 := le_trans (min_le_left _ _) (by norm_num)
  obtain ⟨na, Ca, _hCa, hA⟩ := L6_1a γ p₀ K hadm
  obtain ⟨nb, hB⟩ := L6_1b (α₆ p₀) hα0 hα1
  obtain ⟨nf, hF⟩ := L6_1e_facts (α₆ p₀)
  obtain ⟨nc, hC⟩ := L6_1e_code (α₆ p₀) hα0 hα1
  obtain ⟨nm, Cm, hMain⟩ := section6_main γ p₀ K hadm
  refine ⟨max (max na nb) (max (max nf nc) nm), max Ca (max Cm 1), ?_⟩
  intro n N E G M hL hBal hW hCap hDeg
  have hn : max (max na nb) (max (max nf nc) nm) ≤ n := hL.1
  have hpow : (0 : ℝ) ≤ 2 ^ n := by positivity
  have hLa : LargeAt na Ca n N := ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn,
    le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow) hL.2.1, hL.2.2⟩
  have hLm : LargeAt nm Cm n N := ⟨le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn,
    le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_right _ _)) hpow) hL.2.1,
    hL.2.2⟩
  have hN1 : (1 : ℝ) ≤ N := by
    have h1 : (1 : ℝ) * 2 ^ n ≤ N :=
      le_trans (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) hpow) hL.2.1
    have h2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith
  rcases hA n N E G M hLa hBal hW hCap with hcube | hpar
  · exact hcube
  · obtain ⟨par⟩ := hpar
    obtain ⟨g⟩ := hB n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
    have facts := hF n (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hn)
      g (J₆ g.L.m)
    obtain ⟨code⟩ := hC n (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
      (le_max_right _ _))) hn) g
    have hNpos : 0 < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN1 : (0 : ℝ) < N)
    have hι : Nonempty M.ι := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have h := M.Λ_sum
      simp at h
    let X : Ctx6 γ p₀ K n N E G M :=
      { par := par
        g := g
        facts := facts
        code := code
        y₀ := ⟨0, hNpos⟩
        i₀ := Classical.choice hι
        hBal := hBal
        hWidth := hW
        hCap := hCap
        hDeg := hDeg }
    exact hMain n N E G M X hLm

end

end S06

/-- Public L6.1 export, matching the statement in `scratch-B/StatementsBody.lean`. -/
theorem small_polynomial_broad_side :
    ∃ Dstar > (0 : ℝ), ∀ γ p₀ K : ℝ, 0 < γ → γ < 1 → 0 < p₀ → 0 < K →
      ∃ (n₀ : ℕ) (C₀ : ℝ),
        ∀ (n N : ℕ) (E : Fin N → Fin N → Prop) (G : Colour) (M : TagMix N),
          LargeAt n₀ C₀ n N → M.Balanced K →
          (∀ i, 0 < M.Λ i → (M.μ i).WidthLE ((n : ℝ) ^ γ)) →
          (∀ i, 0 < M.Λ i → (M.ν i).CapLE ((n : ℝ) ^ Dstar)) →
          (∀ i y, 0 < M.Λ i → 0 < (M.ν i).w y →
            1 - (n : ℝ) ^ (-p₀) ≤ colDeg E G (M.μ i) y) →
          CubeAt n N E :=
  S06.small_polynomial_broad_side_core

end HypercubeRamsey
