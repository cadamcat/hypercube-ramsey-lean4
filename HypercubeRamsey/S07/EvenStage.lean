import HypercubeRamsey.S07.EvenStage_q_s07_even
import HypercubeRamsey.S07.AnchorStage
import HypercubeRamsey.S03.ClockSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 1000000

/-!
# L7.1, Steps 5–6: injective odd labels, posterior even rows and even loads

Source: `sections/07-…tex`, lines 313–391.
-/

namespace HypercubeRamsey.S07

open Classical OAI.HypercubeRamsey
open Filter
open scoped BigOperators

/-- L7.1h, clock step (07:313–324): on a successful prehistory, Lemma 3.10 (`clock_sampling` with `B = 3`,
`C_g = 2`) applied to the odd rows (probability laws on valid cells, atoms `≤ L/N ≤ n^{-A}`, column sums
`≤ 10⁻⁸`), with predictive failure at each even role as forbidden predicate (scope its `n` odd neighbours,
product-law probability `r_v ≤ e^{-.02q} ≤ n^{-P}` since no alarm occurs), gives an injective odd assignment
avoiding all predictive failures with joint comparison `1 + ε n ≤ 2` on at most `n^3` rows. -/
theorem clock_rows (d : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι) (W : Γ.Cell → Fin N),
        GeomLocal Γ → RowLaw Γ M → RowCap Γ M → GoodPre Γ M σ W → ∃ J, ClockOK Γ M σ W J := by
  classical
  obtain ⟨A, P₀, nClock, ε, hε, hSampler⟩ :=
    HypercubeRamsey.clock_sampling 3 2 (by norm_num)
  obtain ⟨nCap, hCap⟩ := clockCellCap_small d hd hd'
  let Aabs : ℝ := |A|
  let Pabs : ℝ := |P₀|
  let c : ℝ := 1 / (100 * (Aabs + Pabs + 1))
  have hc : 0 < c := by dsimp [c, Aabs, Pabs]; positivity
  have hAc : Aabs * c ≤ 1 / 100 := by
    dsimp [c]
    have hden : 0 < Aabs + Pabs + 1 := by positivity
    calc
      Aabs * (1 / (100 * (Aabs + Pabs + 1))) =
          Aabs / (100 * (Aabs + Pabs + 1)) := by ring
      _ ≤ 1 / 100 := by
        apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 100) hden)).2
        nlinarith [abs_nonneg A, abs_nonneg P₀]
  have hPc : Pabs * c ≤ 1 / 100 := by
    dsimp [c]
    have hden : 0 < Aabs + Pabs + 1 := by positivity
    calc
      Pabs * (1 / (100 * (Aabs + Pabs + 1))) =
          Pabs / (100 * (Aabs + Pabs + 1)) := by ring
      _ ≤ 1 / 100 := by
        apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 100) hden)).2
        nlinarith [abs_nonneg A, abs_nonneg P₀]
  let α : ℝ := 4 * d
  have hα : 0 < α := by dsimp [α]; positivity
  have hα' : α < 1 / 2 := by dsimp [α]; linarith
  let qfun : ℕ → ℝ := fun n => (gQ d n : ℝ)
  have hqT : Tendsto qfun atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
    exact Filter.tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ) ^ α) (g := qfun)
      (fun n => by simpa [qfun, gQ, α] using (Nat.le_ceil ((n : ℝ) ^ (4 * d)))) hpow
  have hqLower (n : ℕ) : (n : ℝ) ^ α ≤ qfun n := by
    dsimp [qfun, gQ, α]
    exact Nat.le_ceil _
  have hlogDiv : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ α) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlogSmall : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) / (n : ℝ) ^ α < c :=
    hlogDiv.eventually (eventually_lt_nhds hc)
  have hqUpper : ∀ᶠ n : ℕ in atTop, qfun n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    have hbase : 1 ≤ (n : ℝ) ^ α := Real.one_le_rpow hnR hα.le
    have hceil : qfun n ≤ (n : ℝ) ^ α + 1 := by
      dsimp [qfun, gQ]
      exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n : ℝ) ^ (4 * d))).le
    have hpow : (n : ℝ) ^ α ≤ (n : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR hα'.le
    have hroot : 1 ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      exact Real.one_le_rpow hnR (by norm_num)
    dsimp [qfun] at hceil ⊢
    nlinarith
  let t : ℕ → ℕ := fun n => Nat.ceil (Real.exp (c * qfun n))
  have htLower (n : ℕ) : Real.exp (c * qfun n) ≤ (t n : ℝ) := by
    dsimp [t]
    exact Nat.le_ceil _
  have htT : Tendsto (fun n : ℕ => (t n : ℝ)) atTop atTop := by
    have harg : Tendsto (fun n : ℕ => c * qfun n) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hc).2 hqT
    have hexp := (Real.tendsto_exp_atTop).comp harg
    exact Filter.tendsto_atTop_mono (f := fun n : ℕ => Real.exp (c * qfun n))
      (g := fun n => (t n : ℝ)) (fun n => htLower n) hexp
  have htNat : Tendsto t atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro k
    filter_upwards [htT.eventually_ge_atTop (k : ℝ)] with n hn
    exact_mod_cast hn
  have htGeN : ∀ᶠ n : ℕ in atTop, n ≤ t n := by
    filter_upwards [hlogSmall, Filter.eventually_ge_atTop (1 : ℕ)] with n hlog hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hpowpos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnR α
    have hlogn : Real.log (n : ℝ) < c * (n : ℝ) ^ α := (div_lt_iff₀ hpowpos).mp hlog
    have hArg : Real.log (n : ℝ) < c * qfun n := lt_of_lt_of_le hlogn
      (mul_le_mul_of_nonneg_left (hqLower n) hc.le)
    have hreal : (n : ℝ) ≤ (t n : ℝ) := by
      calc
        (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnR).symm
        _ ≤ Real.exp (c * qfun n) := Real.exp_le_exp.mpr hArg.le
        _ ≤ (t n : ℝ) := htLower n
    exact_mod_cast hreal
  have hAerr : ∀ᶠ n : ℕ in atTop, Aabs * (c * qfun n + 1) ≤ (n : ℝ) / 3 := by
    filter_upwards [hqUpper, Filter.eventually_ge_atTop (10000 : ℕ),
      Filter.eventually_ge_atTop (Nat.ceil (12 * Aabs))] with n hqU hn10000 hnA
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hnR10000 : (10000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn10000
    have hnA' : 12 * Aabs ≤ (n : ℝ) := by
      calc
        12 * Aabs ≤ (Nat.ceil (12 * Aabs) : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := by exact_mod_cast hnA
    have hq0 : 0 ≤ qfun n := by dsimp [qfun]; positivity
    have hroot : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) / 100 := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hprod : 0 ≤ (n : ℝ) * ((n : ℝ) - 10000) :=
          mul_nonneg (by positivity) (by linarith)
        nlinarith
    calc
      Aabs * (c * qfun n + 1) = (Aabs * c) * qfun n + Aabs := by ring
      _ ≤ (1 / 100) * qfun n + Aabs := by
        exact add_le_add (mul_le_mul_of_nonneg_right hAc hq0) le_rfl
      _ ≤ (1 / 100) * (2 * (n : ℝ) ^ (1 / 2 : ℝ)) + (n : ℝ) / 12 := by
        exact add_le_add (mul_le_mul_of_nonneg_left hqU (by positivity)) (by nlinarith)
      _ ≤ (n : ℝ) / 3 := by nlinarith [hroot]
  have hPerr : ∀ᶠ n : ℕ in atTop, Pabs * (c * qfun n + 1) ≤ (2 / 100 : ℝ) * qfun n := by
    filter_upwards [hqT.eventually_ge_atTop (100 * Pabs)] with n hqn
    have hqnonneg : 0 ≤ qfun n := by dsimp [qfun]; positivity
    calc
      Pabs * (c * qfun n + 1) = (Pabs * c) * qfun n + Pabs := by ring
      _ ≤ (1 / 100) * qfun n + Pabs := by
        exact add_le_add (mul_le_mul_of_nonneg_right hPc hqnonneg) le_rfl
      _ ≤ (1 / 100) * qfun n + (1 / 100) * qfun n := by
        have hPbound : Pabs ≤ (1 / 100) * qfun n := by nlinarith [hqn]
        exact add_le_add le_rfl hPbound
      _ = (2 / 100 : ℝ) * qfun n := by ring
  have hεsmall : ∀ᶠ n : ℕ in atTop, ε (t n) ≤ 1 := by
    have he : ∀ᶠ k : ℕ in atTop, ε k < 1 := hε.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [htNat.eventually he] with n h
    exact h.le
  have htUpper : ∀ᶠ n : ℕ in atTop,
      (t n : ℝ) ≤ 2 * Real.exp (c * qfun n) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hceil : (t n : ℝ) < Real.exp (c * qfun n) + 1 := by
      dsimp [t]
      exact Nat.ceil_lt_add_one (by positivity)
    have hexpOne : 1 ≤ Real.exp (c * qfun n) := by
      have harg : 0 ≤ c * qfun n := by positivity
      have h := Real.add_one_le_exp (c * qfun n)
      linarith
    linarith
  have hClockParam : ∀ᶠ n : ℕ in atTop, nClock ≤ t n := by
    filter_upwards [htGeN, Filter.eventually_ge_atTop nClock] with n htn hnc
    exact le_trans hnc htn
  have htail : ∀ᶠ n : ℕ in atTop,
      nCap ≤ n ∧ nClock ≤ t n ∧ ε (t n) ≤ 1 ∧ Aabs * (c * qfun n + 1) ≤ (n : ℝ) / 3 ∧
        Pabs * (c * qfun n + 1) ≤ (2 / 100 : ℝ) * qfun n ∧ n ≤ t n ∧
          (t n : ℝ) ≤ 2 * Real.exp (c * qfun n) := by
    filter_upwards [Filter.eventually_ge_atTop nCap, hClockParam,
      hεsmall, hAerr, hPerr, htGeN, htUpper] with n hCapN hClockN heps hAtom hFail htn htu
    exact ⟨hCapN, hClockN, heps, hAtom, hFail, htn, htu⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 htail
  refine ⟨max n₀ 144, 1, ?_⟩
  intro n N hLarge E G X Y p κ Γ M σ W hGeom hrow hcap hpre
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hLarge.1
  have hn144 : 144 ≤ n := le_trans (le_max_right _ _) hLarge.1
  have hNpos : 0 < (N : ℝ) := by
    have hlow : (2 : ℝ) ^ n ≤ (N : ℝ) := by simpa using hLarge.2.1
    exact lt_of_lt_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) _) hlow
  have hNnat : 0 < N := by
    exact_mod_cast hNpos
  have hNlow : (2 : ℝ) ^ n ≤ (N : ℝ) := by simpa using hLarge.2.1
  have hNup : N ≤ n * 2 ^ n := hLarge.2.2
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlogN : Real.log (N : ℝ) ≤ 2 * (n : ℝ) := by
    have hprod : (N : ℝ) ≤ (n : ℝ) * (2 : ℝ) ^ n := by exact_mod_cast hNup
    have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self (le_of_lt hnR)
    have hlog2 := log_two_le_one
    calc
      Real.log (N : ℝ) ≤ Real.log ((n : ℝ) * (2 : ℝ) ^ n) := Real.log_le_log hNpos hprod
      _ = Real.log (n : ℝ) + (n : ℝ) * Real.log 2 := by
        rw [Real.log_mul (ne_of_gt hnR) (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)),
          Real.log_pow]
      _ ≤ (n : ℝ) + (n : ℝ) * 1 :=
        add_le_add hlogn (mul_le_mul_of_nonneg_left hlog2 hnR.le)
      _ = (n : ℝ) + n := by ring
      _ = 2 * (n : ℝ) := by ring
  have htailn := hn₀ n hn0
  have htn : n ≤ t n := htailn.2.2.2.2.2.1
  have htnReal : (n : ℝ) ≤ (t n : ℝ) := by exact_mod_cast htn
  have htnUpper : (t n : ℝ) ≤ 2 * Real.exp (c * qfun n) := htailn.2.2.2.2.2.2
  have hclockN : nClock ≤ t n := htailn.2.1
  have hεn : ε (t n) ≤ 1 := htailn.2.2.1
  have hcapN : cellCap d n (gS d n) ≤ Real.exp ((n : ℝ) / 4) := hCap n htailn.1
  have hatomExp : cellCap d n (gS d n) / (N : ℝ) ≤ Real.exp (-(n : ℝ) / 3) := by
    apply (div_le_iff₀ hNpos).2
    have hNexp : Real.exp ((2 / 3 : ℝ) * n) ≤ (N : ℝ) := by
      have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
        have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
        norm_num at h ⊢
        linarith
      have hbase : Real.exp (2 / 3 : ℝ) ≤ 2 := by
        calc
          Real.exp (2 / 3 : ℝ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hlog2.le
          _ = 2 := by rw [Real.exp_log (by norm_num)]
      have hpow : Real.exp ((2 / 3 : ℝ) * n) = (Real.exp (2 / 3 : ℝ)) ^ n := by
        rw [show (2 / 3 : ℝ) * n = (n : ℝ) * (2 / 3 : ℝ) by ring,
          ← Real.exp_nat_mul]
      calc
        Real.exp ((2 / 3 : ℝ) * n) = (Real.exp (2 / 3 : ℝ)) ^ n := hpow
        _ ≤ (2 : ℝ) ^ n := by gcongr
        _ ≤ (N : ℝ) := hNlow
    have hcap' : cellCap d n (gS d n) ≤ Real.exp ((n : ℝ) / 3) := by
      calc
        cellCap d n (gS d n) ≤ Real.exp ((n : ℝ) / 4) := hcapN
        _ ≤ Real.exp ((n : ℝ) / 3) := Real.exp_le_exp.mpr (by linarith)
    have hprod : Real.exp ((n : ℝ) / 3) ≤ Real.exp (-(n : ℝ) / 3) * Real.exp ((2 / 3 : ℝ) * n) := by
      have harg : (n : ℝ) / 3 = -(n : ℝ) / 3 + (2 / 3 : ℝ) * n := by ring
      rw [harg, Real.exp_add]
    calc
      cellCap d n (gS d n) ≤ Real.exp ((n : ℝ) / 3) := hcap'
      _ ≤ Real.exp (-(n : ℝ) / 3) * Real.exp ((2 / 3 : ℝ) * n) := hprod
      _ ≤ Real.exp (-(n : ℝ) / 3) * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hNexp (Real.exp_nonneg _)
  let pRow : OddRole n → FinProb (Fin N) := fun u =>
    { w := fun y => cellRow Γ M σ W (Γ.key u.1) y
      nonneg := fun y => (hrow σ W (Γ.key u.1)).1 y
      sum_eq_one := by
        have hbad := hpre.1 (Γ.key u.1)
        have hvalid : CellValid Γ M σ W (Γ.key u.1) := by
          have hnotBad : ¬ (¬ CellValid Γ M σ W (Γ.key u.1) ∨
              Alarm Γ M σ W (Γ.key u.1)) := by simpa [CellBad] using hbad
          have hnv : ¬¬CellValid Γ M σ W (Γ.key u.1) := by
            intro hnot
            exact hnotBad (Or.inl hnot)
          exact Classical.not_not.mp hnv
        exact (hrow σ W (Γ.key u.1)).2.2.1 hvalid }
  let zeroLabel : Fin N := ⟨0, hNnat⟩
  let lab : OddRole n → Fin N → Fin N := fun _ y => y
  let failure : EvenRole n → (OddRole n → Fin N) → Prop := fun a f =>
    PredFail Γ M σ W a.1 (nbrLabels f a)
  let scope : EvenRole n → Finset (OddRole n) := clockOddScope
  have hScopeCard : ∀ a : EvenRole n, (scope a).card = n := by
    intro a
    calc
      (scope a).card = (Finset.univ : Finset (Fin n)).card := by
        change (Finset.univ.image (oddNbr a)).card = _
        rw [Finset.card_image_of_injective _ (oddNbr_injective_early a)]
      _ = n := by simp
  have hInc : ∀ u : OddRole n,
      (Finset.univ.filter fun a : EvenRole n => u ∈ scope a).card ≤ n := by
    intro u
    let T : Finset (EvenRole n) := Finset.univ.filter fun a => u ∈ scope a
    let coord : {a : EvenRole n // a ∈ T} → Fin n := fun a =>
      Classical.choose (by
        have hmem : u ∈ scope a.1 := (Finset.mem_filter.mp a.2).2
        rcases Finset.mem_image.mp hmem with ⟨j, hj, huj⟩
        exact ⟨j, huj⟩)
    have hcoord (a : {a : EvenRole n // a ∈ T}) : oddNbr a.1 (coord a) = u :=
      Classical.choose_spec (by
        have hmem : u ∈ scope a.1 := (Finset.mem_filter.mp a.2).2
        rcases Finset.mem_image.mp hmem with ⟨j, hj, huj⟩
        exact ⟨j, huj⟩)
    have hinj : Function.Injective coord := by
      intro a b hab
      have hcoord' := hcoord b
      rw [← hab] at hcoord'
      have hflip : cubeFlip a.1.1 (coord a) = cubeFlip b.1.1 (coord a) :=
        congrArg Subtype.val ((hcoord a).trans hcoord'.symm)
      have htwice := congrArg (fun v => cubeFlip v (coord a)) hflip
      simp [cubeFlip_twice_early] at htwice
      exact Subtype.ext (Subtype.ext htwice)
    have hcardT : T.card ≤ n := by
      calc
        T.card = Fintype.card {a : EvenRole n // a ∈ T} := by
          symm
          exact Fintype.card_coe T
        _ ≤ Fintype.card (Fin n) := Fintype.card_le_of_injective coord hinj
        _ = n := Fintype.card_fin n
    exact hcardT
  have hcol : ∀ y : Fin N, ∑ u : OddRole n, labMarg (pRow u) (lab u) y ≤ 1e-8 := by
    intro y
    have hrowmarg (u : OddRole n) : labMarg (pRow u) (lab u) y =
        cellRow Γ M σ W (Γ.key u.1) y := by
      simp [labMarg, pRow, lab]
    simpa [oddColumn, hrowmarg] using hpre.2 y
  have hCellAtom : ∀ u : OddRole n, ∀ y : Fin N,
      (pRow u).w y ≤ (t n : ℝ) ^ (-A) := by
    intro u y
    have hrowcap : (N : ℝ) * (pRow u).w y ≤ cellCap d n (gS d n) :=
      hcap σ W (Γ.key u.1) y
    have hbase : (pRow u).w y ≤ cellCap d n (gS d n) / (N : ℝ) :=
      (le_div_iff₀ hNpos).2 (by simpa [mul_comm] using hrowcap)
    have htnReal : (n : ℝ) ≤ (t n : ℝ) := by exact_mod_cast htn
    by_cases hA0 : 0 ≤ A
    · have hlogBound : A * (Real.log 2 + c * qfun n) ≤ (n : ℝ) / 3 := by
        have hsumBound := htailn.2.2.2.1
        have hlog2 := log_two_le_one
        calc
          A * (Real.log 2 + c * qfun n) ≤ A * (1 + c * qfun n) := by gcongr
          _ = Aabs * (c * qfun n + 1) := by
            calc
              A * (1 + c * qfun n) = A * (c * qfun n + 1) := by ring
              _ = Aabs * (c * qfun n + 1) := by
                simpa [Aabs, abs_of_nonneg hA0]
          _ ≤ (n : ℝ) / 3 := hsumBound
      have htPos : 0 < (t n : ℝ) := lt_of_lt_of_le (by positivity) htnReal
      have hbasePow : (2 * Real.exp (c * qfun n)) ^ (-A) =
          Real.exp (-A * (Real.log 2 + c * qfun n)) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
        congr 1
        ring
      have hpowCompare :
          (2 * Real.exp (c * qfun n)) ^ (-A) ≤ (t n : ℝ) ^ (-A) :=
        Real.rpow_le_rpow_of_nonpos htPos htnUpper (neg_nonpos.mpr hA0)
      have hexpCompare : Real.exp (-(n : ℝ) / 3) ≤
          Real.exp (-A * (Real.log 2 + c * qfun n)) :=
        Real.exp_le_exp.mpr (by nlinarith [hlogBound])
      calc
        (pRow u).w y ≤ Real.exp (-(n : ℝ) / 3) := le_trans hbase hatomExp
        _ ≤ Real.exp (-A * (Real.log 2 + c * qfun n)) := hexpCompare
        _ = (2 * Real.exp (c * qfun n)) ^ (-A) := hbasePow.symm
        _ ≤ (t n : ℝ) ^ (-A) := hpowCompare
    · have hrowle : (pRow u).w y ≤ 1 := by
        have hsum := (hrow σ W (Γ.key u.1)).2.1
        have hone := Finset.single_le_sum
          (fun z hz => (hrow σ W (Γ.key u.1)).1 z) (Finset.mem_univ y)
        exact hone.trans hsum
      have htOneBase : 1 ≤ (t n : ℝ) := by
        have h1n : 1 ≤ n := by omega
        exact le_trans (by exact_mod_cast h1n) htnReal
      have htOne : 1 ≤ (t n : ℝ) ^ (-A) :=
        Real.one_le_rpow htOneBase (by linarith)
      exact hrowle.trans htOne
  have hLabAtom : ∀ u : OddRole n, ∀ y : Fin N,
      labMarg (pRow u) (lab u) y ≤ (t n : ℝ) ^ (-A) := by
    intro u y
    have hmarg : labMarg (pRow u) (lab u) y = (pRow u).w y := by
      simp [labMarg, lab]
    rw [hmarg]
    exact hCellAtom u y
  have hscopeMem (a : EvenRole n) (j : Fin n) : oddNbr a j ∈ scope a := by
    simp [scope, clockOddScope]
  have hFailureDep : ∀ a : EvenRole n, FinProb.DependsOn (failure a) (scope a) := by
    intro a f f' hagree
    have hlabels : nbrLabels f a = nbrLabels f' a := by
      funext j
      exact hagree (oddNbr a j) (hscopeMem a j)
    simp [failure, hlabels]
  have hPredProbEq (a : EvenRole n) :
      (FinProb.pi pRow).pr (failure a) = alarmRate Γ M σ W a.1 := by
    classical
    let eI := clockOddScopeEquiv a
    let eAss : (∀ u : {u // u ∈ scope a}, Fin N) ≃ (Fin n → Fin N) := {
      toFun := fun z => fun j => z (eI j)
      invFun := fun y => fun u => y (eI.symm u)
      left_inv := by
        intro z
        funext u
        simp
      right_inv := by
        intro y
        funext j
        simp
    }
    let extZ : (∀ u : {u // u ∈ scope a}, Fin N) → OddRole n → Fin N := fun z u =>
      if h : u ∈ scope a then z ⟨u, h⟩ else zeroLabel
    let fz : (∀ u : {u // u ∈ scope a}, Fin N) → ℝ := fun z =>
      if failure a (extZ z) then
        ∏ u : {u // u ∈ scope a}, (pRow u.1).w (z u)
      else 0
    let gy : (Fin n → Fin N) → ℝ := fun y =>
      if PredFail Γ M σ W a.1 y then
        ∏ j, cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j)
      else 0
    have heval (y : Fin n → Fin N) : nbrLabels (extZ (eAss.symm y)) a = y := by
      funext j
      have hmem := hscopeMem a j
      let uj : {u // u ∈ scope a} := ⟨oddNbr a j, hmem⟩
      have heI : eI j = uj := by
        apply Subtype.ext
        rfl
      have heval' : (eAss.symm y) (eI j) = y j := by
        have h := congrFun (eAss.apply_symm_apply y) j
        simpa [eAss] using h
      change extZ (eAss.symm y) (oddNbr a j) = y j
      rw [show extZ (eAss.symm y) (oddNbr a j) = (eAss.symm y) uj by
        simp [extZ, hmem, uj], ← heI]
      exact heval'
    have hfailVal (y : Fin n → Fin N) : failure a (extZ (eAss.symm y)) =
        PredFail Γ M σ W a.1 y := by
      simp [failure, heval]
    have hprod (y : Fin n → Fin N) :
        (∏ u : {u // u ∈ scope a}, (pRow u.1).w ((eAss.symm y) u)) =
          ∏ j, cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j) := by
      have h := Fintype.prod_equiv eI
        (fun j : Fin n => (pRow (eI j).1).w ((eAss.symm y) (eI j)))
        (fun u : {u // u ∈ scope a} => (pRow u.1).w ((eAss.symm y) u))
        (by intro j; rfl)
      have h' := h.symm
      have hpoint : ∀ j : Fin n,
          (pRow (eI j).1).w ((eAss.symm y) (eI j)) =
            cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j) := by
        intro j
        have heval' : (eAss.symm y) (eI j) = y j := by
          exact congrFun (eAss.apply_symm_apply y) j
        rw [heval']
        rfl
      simpa only [hpoint] using h'
    have hdep := hFailureDep a
    rw [pi_pr_dependsOn pRow (scope a) (failure a) hdep (fun _ => zeroLabel)]
    change (∑ z : (∀ u : {u // u ∈ scope a}, Fin N), fz z) =
      ∑ y : Fin n → Fin N,
        (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j)) *
          (if PredFail Γ M σ W a.1 y then 1 else 0)
    calc
      (∑ z : (∀ u : {u // u ∈ scope a}, Fin N), fz z) =
          ∑ y : Fin n → Fin N, fz (eAss.symm y) := by
            exact Fintype.sum_equiv eAss fz (fun y => fz (eAss.symm y))
              (by intro z; exact (congrArg fz (eAss.left_inv z)).symm)
      _ = ∑ y : Fin n → Fin N, gy y := by
            apply Finset.sum_congr rfl
            intro y hy
            change fz (eAss.symm y) = gy y
            change (if failure a (extZ (eAss.symm y)) then
                ∏ u : {u // u ∈ scope a}, (pRow u.1).w ((eAss.symm y) u) else 0) =
              (if PredFail Γ M σ W a.1 y then
                ∏ j, cellRow Γ M σ W (Γ.key (cubeFlip a.1 j)) (y j) else 0)
            rw [hfailVal y]
            by_cases hf : PredFail Γ M σ W a.1 y
            · simp only [hf, ↓reduceIte]
              exact hprod y
            · simp [hf]
      _ = alarmRate Γ M σ W a.1 := by
            unfold alarmRate
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hf : PredFail Γ M σ W a.1 y <;> simp [gy, hf]
  have hNoAlarm : ∀ a : EvenRole n,
      alarmRate Γ M σ W a.1 ≤ Real.exp (-(2 / 100 : ℝ) * gQ d n) := by
    intro a
    have hno : ¬ Alarm Γ M σ W (Γ.key a.1) := by
      intro ha
      apply hpre.1 (Γ.key a.1)
      exact Or.inr ha
    apply le_of_not_gt
    intro hr
    exact hno ⟨a, rfl, hr⟩
  have hFailBound : ∀ a : EvenRole n,
      (FinProb.pi pRow).pr (failure a) ≤ (t n : ℝ) ^ (-P₀) := by
    intro a
    rw [hPredProbEq]
    have hsmallP := htailn.2.2.2.2.1
    by_cases hP0 : 0 ≤ P₀
    · have hlog2 := log_two_le_one
      have hlogBound : P₀ * (Real.log 2 + c * qfun n) ≤ (2 / 100 : ℝ) * qfun n := by
        calc
          P₀ * (Real.log 2 + c * qfun n) ≤ P₀ * (1 + c * qfun n) := by gcongr
          _ = Pabs * (c * qfun n + 1) := by
            calc
              P₀ * (1 + c * qfun n) = P₀ * (c * qfun n + 1) := by ring
              _ = Pabs * (c * qfun n + 1) := by
                simpa [Pabs, abs_of_nonneg hP0]
          _ ≤ (2 / 100 : ℝ) * qfun n := hsmallP
      have htPos : 0 < (t n : ℝ) := by linarith [htnReal]
      have hpow : (2 * Real.exp (c * qfun n)) ^ (-P₀) =
          Real.exp (-P₀ * (Real.log 2 + c * qfun n)) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
        congr 1
        ring
      have hpowcmp : (2 * Real.exp (c * qfun n)) ^ (-P₀) ≤ (t n : ℝ) ^ (-P₀) :=
        Real.rpow_le_rpow_of_nonpos htPos htnUpper (neg_nonpos.mpr hP0)
      exact (hNoAlarm a).trans (by
        calc
          Real.exp (-(2 / 100 : ℝ) * qfun n) ≤
              Real.exp (-P₀ * (Real.log 2 + c * qfun n)) :=
                Real.exp_le_exp.mpr (by nlinarith [hlogBound])
          _ = (2 * Real.exp (c * qfun n)) ^ (-P₀) := hpow.symm
          _ ≤ (t n : ℝ) ^ (-P₀) := hpowcmp)
    · have hExpLeOne : Real.exp (-(2 / 100 : ℝ) * qfun n) ≤ 1 := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        have hq0 : 0 ≤ qfun n := by positivity
        nlinarith
      have htOneBase : 1 ≤ (t n : ℝ) := by
        have h1n : 1 ≤ n := by omega
        exact le_trans (by exact_mod_cast h1n) htnReal
      have htOne : 1 ≤ (t n : ℝ) ^ (-P₀) :=
        Real.one_le_rpow htOneBase (by linarith)
      exact (hNoAlarm a).trans (hExpLeOne.trans htOne)
  have hscope3 : ∀ a : EvenRole n, ((scope a).card : ℝ) ≤ (t n : ℝ) ^ (3 : ℝ) := by
    intro a
    have ht1 : 1 ≤ t n := le_trans (by omega) htn
    have ht3 : t n ≤ (t n) ^ 3 := nat_le_cube ht1
    have hnat : n ≤ (t n) ^ 3 := le_trans htn ht3
    rw [hScopeCard a]
    have hreal : (n : ℝ) ≤ (t n : ℝ) ^ 3 := by exact_mod_cast hnat
    calc
      (n : ℝ) ≤ (t n : ℝ) ^ 3 := hreal
      _ = (t n : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ _).symm
  have hinc3 : ∀ u : OddRole n,
      ((Finset.univ.filter fun a : EvenRole n => u ∈ scope a).card : ℝ) ≤ (t n : ℝ) ^ (3 : ℝ) := by
    intro u
    have ht1 : 1 ≤ t n := le_trans (by omega) htn
    have ht3 : t n ≤ (t n) ^ 3 := nat_le_cube ht1
    have hnat : (Finset.univ.filter fun a : EvenRole n => u ∈ scope a).card ≤ (t n) ^ 3 :=
      le_trans (hInc u) (le_trans htn ht3)
    have hreal : ((Finset.univ.filter fun a : EvenRole n => u ∈ scope a).card : ℝ) ≤
        (t n : ℝ) ^ 3 := by exact_mod_cast hnat
    calc
      ((Finset.univ.filter fun a : EvenRole n => u ∈ scope a).card : ℝ) ≤ (t n : ℝ) ^ 3 := hreal
      _ = (t n : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ _).symm
  have hSbound {S : Finset (OddRole n)} (hS : (S.card : ℝ) ≤ (n : ℝ) ^ 3) :
      (S.card : ℝ) ≤ (t n : ℝ) ^ (3 : ℝ) := by
    have hSreal : (S.card : ℝ) ≤ (n : ℝ) ^ (3 : ℝ) := by
      calc
        (S.card : ℝ) ≤ (n : ℝ) ^ 3 := hS
        _ = (n : ℝ) ^ (3 : ℝ) := (Real.rpow_natCast _ _).symm
    calc
      (S.card : ℝ) ≤ (n : ℝ) ^ (3 : ℝ) := hSreal
      _ ≤ (t n : ℝ) ^ (3 : ℝ) := by
        exact Real.rpow_le_rpow (by positivity) htnReal (by norm_num : 0 ≤ (3 : ℝ))
  have hdepfailure : ∀ a : EvenRole n, FinProb.DependsOn (failure a) (scope a) := by
    exact hFailureDep
  have hlogN' : Real.log (N : ℝ) ≤ 2 * (t n : ℝ) := by
    nlinarith [hlogN, htnReal]
  have hSamplerCall := hSampler (t n) hclockN N hlogN' lab pRow failure scope
    hcol hLabAtom hdepfailure (fun a => by simpa using hscope3 a)
    (fun u => by simpa using hinc3 u) hFailBound
  obtain ⟨J, hJsupp, hJ⟩ := hSamplerCall
  have hεlower : 0 ≤ ε (t n) := by
    have hEmpty := hJ ∅ (fun _ : OddRole n => zeroLabel) (by simp)
    have hpr : J.pr (fun _ => True) = 1 := by
      unfold FinProb.pr
      simp [J.sum_eq_one]
    have hEmpty' : 1 ≤ 1 + ε (t n) := by simpa [hpr] using hEmpty
    linarith
  have hfactor : 0 ≤ 1 + ε (t n) ∧ 1 + ε (t n) ≤ 2 := by
    constructor <;> linarith [hεlower, hεn]
  refine ⟨J, ?_⟩
  constructor
  · intro f hf
    have h := hJsupp f hf
    constructor
    · simpa [lab] using h.1
    · intro a
      exact h.2 a
  · intro S o hS
    have hbound := hJ S o (hSbound hS)
    have hprod : 0 ≤ ∏ u ∈ S, (pRow u).w (o u) :=
      Finset.prod_nonneg fun u hu => (pRow u).nonneg (o u)
    calc
      J.pr (fun f => ∀ u ∈ S, f u = o u) ≤
          (1 + ε (t n)) * ∏ u ∈ S, (pRow u).w (o u) := hbound
      _ ≤ 2 * ∏ u ∈ S, (pRow u).w (o u) :=
        mul_le_mul_of_nonneg_right hfactor.2 hprod

section Nodes

variable {d : ℝ} {n s ℓ q N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
  {p κ : ℝ}

/-- L7.1i, cancellation (07:363–373): integrating the role's anchor and its product neighbour data gives the
data subdensity `M_v`, which cancels the posterior denominator:
`Σ_y M_v(y) F_x(y) μ(x) / M_v(y) ≤ μ(x) Σ_y F_x(y) ≤ μ(x)`; predictive success only decreases the integral. -/
theorem star_cancel (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ)
    (hupd : StarRefUpdate Γ M) (hrow : RowLaw Γ M) (σ : Γ.Key → M.ι) : StarCancel Γ M σ := by
  classical
  intro W a x
  let key : Γ.Cell := Γ.key a.1
  let μ : Fin N → ℝ := fun z => (M.μ (σ key.1)).w z
  let L : Fin N → (Fin n → Fin N) → ℝ := fun z y =>
    ∏ j, cellRow Γ M σ (Function.update W key z) (Γ.key (cubeFlip a.1 j)) (y j)
  let D : (Fin n → Fin N) → ℝ := fun y => ∑ z, μ z * L z y
  have hupdate (z t : Fin N) :
      Function.update (Function.update W key z) key t = Function.update W key t := by
    funext c
    by_cases hc : c = key <;> simp [hc]
  have hLrewrite (z t : Fin N) (y : Fin n → Fin N) :
      starLik Γ M σ (Function.update W key z) a.1 t y = L t y := by
    dsimp [L, starLik]
    rw [hupdate z t]
  have hMarg (z : Fin N) (y : Fin n → Fin N) :
      starMarg Γ M σ (Function.update W key z) a.1 y = D y := by
    unfold starMarg D μ
    apply Finset.sum_congr rfl
    intro t ht
    rw [hLrewrite z t y]
  have hRef (z : Fin N) (y : Fin n → Fin N) :
      starRef Γ M σ (Function.update W key z) a.1 y = starRef Γ M σ W a.1 y := by
    exact congrFun (hupd σ W a.1 z) y
  have hFail (z : Fin N) (y : Fin n → Fin N) :
      PredFail Γ M σ (Function.update W key z) a.1 y =
        (D y = 0 ∨ D y < Real.exp (-(4 / 100 : ℝ) * q) * starRef Γ M σ W a.1 y) := by
    simp only [PredFail, hMarg z y, hRef z y]
  have hLnonneg (z : Fin N) (y : Fin n → Fin N) : 0 ≤ L z y := by
    unfold L
    apply Finset.prod_nonneg
    intro j hj
    exact (hrow σ (Function.update W key z) (Γ.key (cubeFlip a.1 j))).1 (y j)
  have hDsum (y : Fin n → Fin N) : (∑ z, μ z * L z y) = D y := rfl
  have hLsum (z : Fin N) : ∑ y : Fin n → Fin N, L z y ≤ 1 := by
    calc
      (∑ y, L z y) = ∏ j, ∑ t, cellRow Γ M σ (Function.update W key z)
          (Γ.key (cubeFlip a.1 j)) t := by
        unfold L
        rw [← Fintype.prod_sum]
      _ ≤ ∏ j, 1 := by
        calc
          ∏ j, ∑ t, cellRow Γ M σ (Function.update W key z)
              (Γ.key (cubeFlip a.1 j)) t ≤ 1 := by
            apply Finset.prod_le_one₀
            · intro j hj
              apply Finset.sum_nonneg
              intro t ht
              exact (hrow σ (Function.update W key z) (Γ.key (cubeFlip a.1 j))).1 t
            · intro j hj
              exact (hrow σ (Function.update W key z) (Γ.key (cubeFlip a.1 j))).2.1
          _ = ∏ j : Fin n, (1 : ℝ) := by simp
      _ = 1 := by simp
  have hexpand :
      (∑ z, μ z * evenStar Γ M σ (Function.update W key z) a x) =
        ∑ y : Fin n → Fin N, ∑ z, μ z *
          (L z y * ((if PredFail Γ M σ (Function.update W key z) a.1 y then 0 else 1) *
            ((N : ℝ) * (L x y * μ x / D y)))) := by
    unfold evenStar
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro z hz
    simp only [evenRowAt]
    rw [hLrewrite z x y, hMarg z y]
  have hinner (y : Fin n → Fin N) :
      (∑ z, μ z * (L z y *
        ((if PredFail Γ M σ (Function.update W key z) a.1 y then 0 else 1) *
          ((N : ℝ) * (L x y * μ x / D y))))) ≤ (N : ℝ) * μ x * L x y := by
    by_cases hbad : D y = 0 ∨ D y < Real.exp (-(4 / 100 : ℝ) * q) * starRef Γ M σ W a.1 y
    · have hzero : ∀ z : Fin N,
          μ z * (L z y *
            ((if PredFail Γ M σ (Function.update W key z) a.1 y then 0 else 1) *
              ((N : ℝ) * (L x y * μ x / D y)))) = 0 := by
        intro z
        have hpred : PredFail Γ M σ (Function.update W key z) a.1 y := by
          rw [hFail z y]
          exact hbad
        simp [hpred]
      rw [Finset.sum_eq_zero (fun z hz => hzero z)]
      exact mul_nonneg (mul_nonneg (by positivity) ((M.μ (σ key.1)).nonneg x)) (hLnonneg x y)
    · have hDne : D y ≠ 0 := by
        intro hz
        exact hbad (Or.inl hz)
      calc
        (∑ z, μ z * (L z y *
          ((if PredFail Γ M σ (Function.update W key z) a.1 y then 0 else 1) *
            ((N : ℝ) * (L x y * μ x / D y))))) =
          ∑ z, (μ z * L z y) * ((N : ℝ) * (L x y * μ x / D y)) := by
            apply Finset.sum_congr rfl
            intro z hz
            have hpred : ¬ PredFail Γ M σ (Function.update W key z) a.1 y := by
              rw [hFail z y]
              exact hbad
            simp [hpred]
            ring
        _ = (∑ z, μ z * L z y) * ((N : ℝ) * (L x y * μ x / D y)) := by
            rw [Finset.sum_mul]
        _ = (N : ℝ) * μ x * L x y := by
            rw [hDsum y]
            field_simp [hDne]
        _ ≤ (N : ℝ) * μ x * L x y := le_rfl
  calc
    (∑ z, μ z * evenStar Γ M σ (Function.update W key z) a x) =
        ∑ y : Fin n → Fin N, ∑ z, μ z *
          (L z y * ((if PredFail Γ M σ (Function.update W key z) a.1 y then 0 else 1) *
            ((N : ℝ) * (L x y * μ x / D y)))) := hexpand
    _ ≤ ∑ y : Fin n → Fin N, (N : ℝ) * μ x * L x y := by
      apply Finset.sum_le_sum
      intro y hy
      exact hinner y
    _ ≤ (N : ℝ) * μ x := by
      calc
        _ = ((N : ℝ) * μ x) * (∑ y : Fin n → Fin N, L x y) := by
          rw [Finset.mul_sum]
        _ ≤ (N : ℝ) * μ x * 1 :=
          mul_le_mul_of_nonneg_left (hLsum x)
            (mul_nonneg (by positivity) ((M.μ (σ key.1)).nonneg x))
        _ = (N : ℝ) * (M.μ (σ key.1)).w x := by simp [μ]

/-- L7.1i, clock comparison (07:347–352): the separated roles have disjoint odd neighbourhoods, the clock law is
supported on predictive success, and its joint comparison on the at most `n²` neighbouring odd labels replaces
the injection by independent draws from the odd rows; the integral then factors into the star integrals. -/
theorem clock_factor (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hrow : RowLaw Γ M)
    (σ : Γ.Key → M.ι) (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N))
    (hJ : ∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) : ClockFactor Γ M σ J := by
  intro W hpre x m hm a hsep
  classical
  have hvalid (c : Γ.Cell) : CellValid Γ M σ W c := by
    by_contra hbad
    exact hpre.1 c (Or.inl hbad)
  let row : OddRole n → FinProb (Fin N) := fun u =>
    { w := fun y => cellRow Γ M σ W (Γ.key u.1) y
      nonneg := fun y => (hrow σ W (Γ.key u.1)).1 y
      sum_eq_one := (hrow σ W (Γ.key u.1)).2.2.1 (hvalid (Γ.key u.1)) }
  let neigh : Fin m → Finset (OddRole n) := fun i =>
    Finset.univ.image (oddNbr (a i))
  have hneigh_disj : ∀ i j, i ≠ j → Disjoint (neigh i) (neigh j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    rcases Finset.mem_image.mp hui with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp huj with ⟨t, ht, hEq⟩
    have hclose := auxDist_le_two_of_shared_neighbor Γ (a i) (a j) r t hEq.symm
    have hfar := hsep i j hij
    omega
  let S : Finset (OddRole n) := Finset.univ.biUnion neigh
  have hmemNbr (i : Fin m) (j : Fin n) : oddNbr (a i) j ∈ S := by
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hneigh_card (i : Fin m) : (neigh i).card = n := by
    dsimp [neigh]
    rw [Finset.card_image_of_injective _ (oddNbr_injective (a i))]
    simp
  have hScard : (S.card : ℝ) ≤ (n : ℝ) ^ 3 := by
    calc
      (S.card : ℝ) ≤ ∑ i : Fin m, ((neigh i).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := neigh))
      _ = (m : ℝ) * (n : ℝ) := by simp [hneigh_card, mul_comm]
      _ ≤ (n : ℝ) ^ 3 := by
        by_cases hn0 : n = 0
        · subst n
          have hm0 : m = 0 := by omega
          simp [hm0]
        · have hn1 : 1 ≤ (n : ℝ) := by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
          have hmle : (m : ℝ) ≤ n := by exact_mod_cast hm
          calc
            (m : ℝ) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) :=
              mul_le_mul_of_nonneg_right hmle (by positivity)
            _ ≤ (n : ℝ) ^ 3 := by
              calc
                (n : ℝ) * (n : ℝ) = 1 * ((n : ℝ) * (n : ℝ)) := by ring
                _ ≤ (n : ℝ) * ((n : ℝ) * (n : ℝ)) :=
                  mul_le_mul_of_nonneg_right hn1 (by positivity)
                _ = (n : ℝ) ^ 3 := by ring
  let rowSub : {u // u ∈ S} → FinProb (Fin N) := fun u => row u.1
  let refLaw : FinProb (∀ u : {u // u ∈ S}, Fin N) := FinProb.pi rowSub
  let restrict : (OddRole n → Fin N) → (∀ u : {u // u ∈ S}, Fin N) :=
    fun f u => f u.1
  let marginal : FinProb (∀ u : {u // u ∈ S}, Fin N) := FinProb.map (J W) restrict
  let nbrSub (i : Fin m) (j : Fin n) : {u // u ∈ S} := ⟨oddNbr (a i) j, hmemNbr i j⟩
  let scope : Fin m → Finset {u // u ∈ S} := fun i => Finset.univ.image (nbrSub i)
  let localLabels (i : Fin m) (o : ∀ u : {u // u ∈ S}, Fin N) : Fin n → Fin N :=
    fun j => o (nbrSub i j)
  let localFactor (i : Fin m) (o : ∀ u : {u // u ∈ S}, Fin N) : ℝ :=
    (if PredFail Γ M σ W (a i).1 (localLabels i o) then 0 else 1) *
      ((N : ℝ) * evenRowAt Γ M σ W (a i) (localLabels i o) x)
  let factors : Fin m → (∀ u : {u // u ∈ S}, Fin N) → ℝ := localFactor
  let integrand (o : ∀ u : {u // u ∈ S}, Fin N) : ℝ := ∏ i, factors i o
  have hscope_disj : ∀ i j, i ≠ j → Disjoint (scope i) (scope j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    rcases Finset.mem_image.mp hui with ⟨r, hr, rfl⟩
    rcases Finset.mem_image.mp huj with ⟨t, ht, hEq⟩
    have hrole : oddNbr (a i) r = oddNbr (a j) t := by
      simpa [nbrSub] using congrArg Subtype.val hEq.symm
    have h1 : oddNbr (a i) r ∈ neigh i := Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
    have h2 : oddNbr (a i) r ∈ neigh j := by
      rw [hrole]
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
    exact (Finset.disjoint_left.mp (hneigh_disj i j hij) h1) h2
  have hdepends : ∀ i, FinProb.DependsOn (factors i) (scope i) := by
    intro i o o' hagree
    have hlabels : localLabels i o = localLabels i o' := by
      funext j
      exact hagree (nbrSub i j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp [factors, localFactor, hlabels]
  have hfactor : refLaw.expect integrand =
      ∏ i : Fin m, refLaw.expect (factors i) := by
    exact pi_expect_prod_disjoint rowSub scope hscope_disj factors hdepends
  let e_i (i : Fin m) : Fin n ≃ {u // u ∈ scope i} := by
    refine Equiv.ofBijective (fun j => ⟨nbrSub i j, ?_⟩) ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    · intro j k hjk
      have hval : oddNbr (a i) j = oddNbr (a i) k :=
        congrArg (fun z : {u // u ∈ scope i} => z.1.1) hjk
      exact oddNbr_injective (a i) hval
    · intro u
      rcases Finset.mem_image.mp u.2 with ⟨j, hj, hEq⟩
      exact ⟨j, Subtype.ext hEq⟩
  let eAss (i : Fin m) :
      (∀ u : {u // u ∈ scope i}, Fin N) ≃ (Fin n → Fin N) := {
    toFun := fun z : (∀ u : {u // u ∈ scope i}, Fin N) => fun j : Fin n => z (e_i i j)
    invFun := fun y : (Fin n → Fin N) => fun u : {u // u ∈ scope i} => y ((e_i i).symm u)
    left_inv := by
      intro z
      funext u
      simp
    right_inv := by
      intro y
      funext j
      simp
  }
  have heval (i : Fin m) (j : Fin n) : (e_i i j).1.1 = oddNbr (a i) j := rfl
  let localPiFactor (i : Fin m) (z : ∀ u : {u // u ∈ scope i}, Fin N) : ℝ :=
    (if PredFail Γ M σ W (a i).1 (fun j => z (e_i i j)) then 0 else 1) *
      ((N : ℝ) * evenRowAt Γ M σ W (a i) (fun j => z (e_i i j)) x)
  let localPiLaw (i : Fin m) := FinProb.pi (fun u : {u // u ∈ scope i} => rowSub u.1)
  have hproj (i : Fin m) : factors i = fun o => localPiFactor i (fun u => o u.1) := by
    funext o
    dsimp [factors, localFactor, localPiFactor, localLabels]
    congr 1
  have hLocalMarg (i : Fin m) : refLaw.expect (factors i) =
      (localPiLaw i).expect (localPiFactor i) := by
    rw [hproj i]
    exact FinProb.pi_marginal_expect rowSub (scope i) (localPiFactor i)
  have hLocalRow (i : Fin m) : (localPiLaw i).expect (localPiFactor i) =
      evenStar Γ M σ W (a i) x := by
    classical
    unfold FinProb.expect
    change (∑ z : (∀ u : {u // u ∈ scope i}, Fin N),
        (∏ u, (rowSub u.1).w (z u)) * localPiFactor i z) =
      ∑ y : Fin n → Fin N,
        (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip (a i).1 j)) (y j)) *
          ((if PredFail Γ M σ W (a i).1 y then 0 else 1) *
            ((N : ℝ) * evenRowAt Γ M σ W (a i) y x))
    let fz : (∀ u : {u // u ∈ scope i}, Fin N) → ℝ := fun z =>
      (∏ u, (rowSub u.1).w (z u)) * localPiFactor i z
    let gy : (Fin n → Fin N) → ℝ := fun y =>
      (∏ j, cellRow Γ M σ W (Γ.key (cubeFlip (a i).1 j)) (y j)) *
        ((if PredFail Γ M σ W (a i).1 y then 0 else 1) *
          ((N : ℝ) * evenRowAt Γ M σ W (a i) y x))
    have hprod (y : Fin n → Fin N) :
        (∏ u : {u // u ∈ scope i}, (rowSub u.1).w ((eAss i).symm y u)) =
          ∏ j : Fin n, cellRow Γ M σ W (Γ.key (cubeFlip (a i).1 j)) (y j) := by
      have h := Fintype.prod_equiv (e_i i)
        (fun j : Fin n => (rowSub (e_i i j).1).w ((eAss i).symm y (e_i i j)))
        (fun u : {u // u ∈ scope i} => (rowSub u.1).w ((eAss i).symm y u))
        (by intro j; rfl)
      have h' := h.symm
      have hpoint : ∀ j : Fin n,
          (rowSub (e_i i j).1).w ((eAss i).symm y (e_i i j)) =
            cellRow Γ M σ W (Γ.key (cubeFlip (a i).1 j)) (y j) := by
        intro j
        rw [show (eAss i).symm y (e_i i j) = y j by simp [eAss]]
        change (row ((e_i i j).1.1)).w (y j) = _
        rw [heval i j]
        rfl
      simpa only [hpoint] using h'
    calc
      (∑ z : (∀ u : {u // u ∈ scope i}, Fin N), fz z) =
          ∑ y : Fin n → Fin N, fz ((eAss i).symm y) := by
            exact Fintype.sum_equiv (eAss i) fz (fun y => fz ((eAss i).symm y))
              (by intro z; exact (congrArg fz ((eAss i).left_inv z)).symm)
      _ = ∑ y : Fin n → Fin N, gy y := by
        apply Finset.sum_congr rfl
        intro y hy
        simp only [fz, gy, localPiFactor]
        rw [hprod y]
        have hcoord (j : Fin n) : (eAss i).symm y (e_i i j) = y j :=
          congrFun ((eAss i).right_inv y) j
        simp_rw [hcoord]
      _ = evenStar Γ M σ W (a i) x := rfl
  have hlocalFactor_nonneg (i : Fin m) (o : ∀ u : {u // u ∈ S}, Fin N) :
      0 ≤ factors i o := by
    by_cases hfail : PredFail Γ M σ W (a i).1 (localLabels i o)
    · simp [factors, localFactor, hfail]
    · simp only [factors, localFactor, if_neg hfail, one_mul]
      exact mul_nonneg (by positivity)
        (evenRowAt_nonneg_of_success Γ M hrow σ W (a i) (localLabels i o) x hfail)
  have hintegrand_nonneg (o : ∀ u : {u // u ∈ S}, Fin N) : 0 ≤ integrand o :=
    Finset.prod_nonneg fun i hi => hlocalFactor_nonneg i o
  have hnonempty : Nonempty (OddRole n → Fin N) := by
    by_contra h
    haveI : IsEmpty (OddRole n → Fin N) := ⟨fun f => h ⟨f⟩⟩
    have hsum : (∑ f : OddRole n → Fin N, (J W).w f) = 0 := by simp
    rw [(J W).sum_eq_one] at hsum
    norm_num at hsum
  let f₀ : OddRole n → Fin N := Classical.choice hnonempty
  let extend (o : ∀ u : {u // u ∈ S}, Fin N) : OddRole n → Fin N :=
    fun u => if hu : u ∈ S then o ⟨u, hu⟩ else f₀ u
  have hmapWeight (o : ∀ u : {u // u ∈ S}, Fin N) :
      marginal.w o = (J W).pr (fun f => ∀ u : {u // u ∈ S}, f u.1 = o u) := by
    classical
    unfold marginal FinProb.map FinProb.pr
    apply Finset.sum_congr rfl
    intro f hf
    have heq : (restrict f = o) ↔ ∀ u : {u // u ∈ S}, f u.1 = o u := by
      constructor
      · intro h u
        exact congrFun h u
      · intro h
        funext u
        exact h u
    by_cases h : restrict f = o
    · have hevent := heq.mp h
      simp only [if_pos h, if_pos hevent]
    · have hevent : ¬ ∀ u : {u // u ∈ S}, f u.1 = o u := fun hh => h (heq.mpr hh)
      simp only [if_neg h, if_neg hevent]
  have hrefWeight (o : ∀ u : {u // u ∈ S}, Fin N) :
      refLaw.w o = ∏ u : {u // u ∈ S}, cellRow Γ M σ W (Γ.key u.1) (o u) := by
    rfl
  have hrowWeight (o : ∀ u : {u // u ∈ S}, Fin N) :
      (∏ u ∈ S, cellRow Γ M σ W (Γ.key u) (extend o u)) =
        ∏ u : {u // u ∈ S}, cellRow Γ M σ W (Γ.key u.1) (o u) := by
    calc
      (∏ u ∈ S, cellRow Γ M σ W (Γ.key u) (extend o u)) =
          ∏ u : {u // u ∈ S}, cellRow Γ M σ W (Γ.key u.1) (extend o u.1) := by
            symm
            rw [Finset.univ_eq_attach]
            exact Finset.prod_attach S
              (fun u => cellRow Γ M σ W (Γ.key u) (extend o u))
      _ = ∏ u : {u // u ∈ S}, cellRow Γ M σ W (Γ.key u.1) (o u) := by
            apply Finset.prod_congr rfl
            intro u hu
            simp [extend, u.2]
  have hrectBound (o : ∀ u : {u // u ∈ S}, Fin N) : marginal.w o ≤ 2 * refLaw.w o := by
    rw [hmapWeight]
    have h := (hJ W hpre).2 S (extend o) hScard
    have hEventEq : (fun f : OddRole n → Fin N => ∀ u : {u // u ∈ S}, f u.1 = o u) =
        (fun f : OddRole n → Fin N => ∀ u ∈ S, f u = extend o u) := by
      funext f
      apply propext
      constructor
      · intro h u hu
        have hu' : extend o u = o ⟨u, hu⟩ := by simp [extend, hu]
        simpa [hu'] using h ⟨u, hu⟩
      · intro h u
        have h' := h u.1 u.2
        simpa [extend, u.2] using h'
    rw [← hEventEq] at h
    calc
      (J W).pr (fun f => ∀ u : {u // u ∈ S}, f u.1 = o u) ≤
          2 * ∏ u ∈ S, cellRow Γ M σ W (Γ.key u) (extend o u) := h
      _ = 2 * refLaw.w o := by rw [hrowWeight o, ← hrefWeight o]
  have hclockOK := hJ W hpre
  have hleft :
      (∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRow Γ M σ W f (a i) x) =
        (J W).expect (fun f => integrand (restrict f)) := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hweight : (J W).w f = 0
    · simp [hweight]
    · have hsupp := hclockOK.1 f hweight
      have hG : integrand (restrict f) =
          ∏ i, (N : ℝ) * evenRow Γ M σ W f (a i) x := by
        unfold integrand factors localFactor
        apply Finset.prod_congr rfl
        intro i hi
        have hsuccess_i := hsupp.2 (a i)
        have hlabels : localLabels i (restrict f) = nbrLabels f (a i) := by
          funext j
          rfl
        have hpred : ¬ PredFail Γ M σ W (a i).1 (localLabels i (restrict f)) := by
          rw [hlabels]
          exact hsuccess_i
        simp only [if_neg hpred, one_mul]
        rw [hlabels]
        rfl
      exact congrArg (fun y : ℝ => (J W).w f * y) hG.symm
  have hmapExpect : marginal.expect integrand =
      (J W).expect (fun f => integrand (restrict f)) :=
    FinProb.map_expect (J W) restrict integrand
  have hstar : ∏ i : Fin m, refLaw.expect (factors i) =
      ∏ i : Fin m, evenStar Γ M σ W (a i) x := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hLocalMarg i, hLocalRow i]
  calc
    (∑ f, (J W).w f * ∏ i, (N : ℝ) * evenRow Γ M σ W f (a i) x) =
        marginal.expect integrand := by rw [hleft, hmapExpect.symm]
    _ ≤ 2 * refLaw.expect integrand := by
      calc
        marginal.expect integrand = ∑ o, marginal.w o * integrand o := rfl
        _ ≤ ∑ o, (2 * refLaw.w o) * integrand o := by
          apply Finset.sum_le_sum
          intro o ho
          exact mul_le_mul_of_nonneg_right (hrectBound o) (hintegrand_nonneg o)
        _ = 2 * refLaw.expect integrand := by
          simp [FinProb.expect, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    _ = 2 * ∏ i : Fin m, evenStar Γ M σ W (a i) x := by rw [hfactor, hstar]

/-- L7.1i, assembled moment (07:375–380): the clock comparison at every successful prehistory and the anchor
integral give `4^m ∏ N μ(x)` (for `m = 0` both sides are at most one). -/
theorem even_moment (Γ : GridGeom d n s ℓ q) (M : Menu7 n N E G X Y d p κ) (hrow : RowLaw Γ M)
    (σ : Γ.Key → M.ι) (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N))
    (hfac : ClockFactor Γ M σ J) (hint : EvenAnchorIntegral Γ M σ) : EvenMoment Γ M σ J := by
  intro x m hm a hsep
  classical
  by_cases hm0 : m = 0
  · subst m
    simp only [Finset.prod_empty, pow_zero, one_mul]
    calc
      (∑ W, (anchorLaw Γ M σ).w W *
          (if GoodPre Γ M σ W then
            ∑ f, (J W).w f * ∏ i : Fin 0, (N : ℝ) * evenRow Γ M σ W f (a i) x
           else 0))
          ≤ ∑ W, (anchorLaw Γ M σ).w W := by
        apply Finset.sum_le_sum
        intro W hW
        have hsumW : ∑ f : OddRole n → Fin N, (J W).w f = 1 := (J W).sum_eq_one
        by_cases hpre : GoodPre Γ M σ W
        · simp [hpre, hsumW]
        · simp [hpre, (anchorLaw Γ M σ).nonneg W]
      _ = 1 := (anchorLaw Γ M σ).sum_eq_one
  · have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hbase_nonneg : 0 ≤ ∏ i : Fin m,
        (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x :=
      Finset.prod_nonneg fun i hi => mul_nonneg (by positivity)
        ((M.μ (σ (Γ.key (a i).1).1)).nonneg x)
    have hpoint : ∀ W : Γ.Cell → Fin N,
        (if GoodPre Γ M σ W then
          ∑ f, (J W).w f * ∏ i : Fin m, (N : ℝ) * evenRow Γ M σ W f (a i) x
         else 0) ≤ 2 * ∏ i : Fin m, evenStar Γ M σ W (a i) x := by
      intro W
      by_cases hpre : GoodPre Γ M σ W
      · simpa [hpre] using hfac W hpre x m hm a hsep
      · simp only [hpre, ↓reduceIte]
        have hnonneg : 0 ≤ ∏ i : Fin m, evenStar Γ M σ W (a i) x :=
          Finset.prod_nonneg fun i hi => evenStar_nonneg Γ M hrow σ W (a i) x
        exact mul_nonneg (by norm_num) hnonneg
    have hsum_bound :
        (∑ W, (anchorLaw Γ M σ).w W *
          (if GoodPre Γ M σ W then
            ∑ f, (J W).w f * ∏ i : Fin m, (N : ℝ) * evenRow Γ M σ W f (a i) x
           else 0)) ≤
        2 * (anchorLaw Γ M σ).expect (fun W => ∏ i : Fin m, evenStar Γ M σ W (a i) x) := by
      calc
        _ ≤ ∑ W, (anchorLaw Γ M σ).w W *
            (2 * ∏ i : Fin m, evenStar Γ M σ W (a i) x) := by
          apply Finset.sum_le_sum
          intro W hW
          exact mul_le_mul_of_nonneg_left (hpoint W) ((anchorLaw Γ M σ).nonneg W)
        _ = 2 * (anchorLaw Γ M σ).expect (fun W => ∏ i : Fin m, evenStar Γ M σ W (a i) x) := by
          simp [FinProb.expect, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
    have hanchor := hint x m hm a hsep
    have hpow : 2 * (2 : ℝ) ^ m ≤ (4 : ℝ) ^ m := by
      calc
        2 * (2 : ℝ) ^ m = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ (2 * m) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
        _ = (4 : ℝ) ^ m := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    calc
      (∑ W, (anchorLaw Γ M σ).w W *
          (if GoodPre Γ M σ W then
            ∑ f, (J W).w f * ∏ i : Fin m, (N : ℝ) * evenRow Γ M σ W f (a i) x
           else 0))
          ≤ 2 * (anchorLaw Γ M σ).expect (fun W => ∏ i : Fin m, evenStar Γ M σ W (a i) x) := hsum_bound
      _ ≤ 2 * (2 ^ m * ∏ i : Fin m, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x) :=
        mul_le_mul_of_nonneg_left hanchor (by norm_num)
      _ ≤ (4 : ℝ) ^ m * ∏ i : Fin m, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x := by
        calc
          2 * (2 ^ m * ∏ i : Fin m, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x) =
              (2 * 2 ^ m) * ∏ i : Fin m, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x := by ring
          _ ≤ (4 : ℝ) ^ m * ∏ i : Fin m, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x :=
            mul_le_mul_of_nonneg_right hpow hbase_nonneg

end Nodes

/-- L7.1i, anchor integral (07:354–380): remove the cell events touching the separated target anchors (at most
`(2s+q+1)²` each, factor `2` per role); the remaining events do not read the targets, each star integral reads
anchors within distance two of its own target only (targets are at auxiliary distance at least six), so the
targets integrate independently and `star_cancel` bounds each factor. -/
theorem even_anchor_integral (D₀ d : ℝ) (hD₀ : 0 < D₀) (hd : 0 < d) (hd' : d < D₀ / 1000) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)}
      {p κ : ℝ} (Γ : Geom d n) (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι),
      CondProductBound → GeomFacts Γ → RowLaw Γ M → AnchorLLL Γ M D₀ σ → StarCancel Γ M σ →
      EvenAnchorIntegral Γ M σ := by
  classical
  obtain ⟨nCharge, hCharge⟩ := anchorChargeSmall D₀ d hD₀ hd hd'
  refine ⟨max nCharge 2, ?_⟩
  intro n hn N E G X Y p κ Γ M σ hCond hGeom hrow hAnchor hStar
  intro x m hm a hsep
  have hnCharge : nCharge ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hchargeSmall :
      ((2 * gS d n + gQ d n + 1 : ℕ) : ℝ) ^ 2 * xL D₀ n ≤ 1 / 2 :=
    hCharge n hnCharge
  let R : ℕ := 2 * gS d n + gQ d n + 1
  let Rr : ℝ := R
  let rawP : Γ.Cell → FinProb (Fin N) := fun c => M.μ (σ c.1)
  let bad : Γ.Cell → (Γ.Cell → Fin N) → Prop := fun c W => CellBad Γ M σ W c
  let badScope : Γ.Cell → Finset Γ.Cell := fun c => Γ.cellBall c 2
  let U : Finset Γ.Cell := Finset.univ.image (fun i : Fin m => Γ.key (a i).1)
  let centerCell : Fin m → Γ.Cell := fun i => Γ.key (a i).1
  have hcenterInjective : Function.Injective centerCell := by
    intro i j hij
    by_contra hne
    have hfar := hsep i j hne
    have hij' : Γ.key (a i).1 = Γ.key (a j).1 := by simpa [centerCell] using hij
    rw [hij'] at hfar
    have hzero : Γ.auxDist (Γ.key (a j).1).2 (Γ.key (a j).1).2 = 0 := by
      simp [GridGeom.auxDist]
    rw [hzero] at hfar
    omega
  have hUcard : U.card = m := by
    dsimp [U]
    rw [Finset.card_image_of_injective _ hcenterInjective]
    simp
  have hcenterMem (i : Fin m) : centerCell i ∈ U :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let targetLaw : {c // c ∈ U} → FinProb (Fin N) := fun c => rawP c.1
  let targetScope : Fin m → Finset {c // c ∈ U} := fun i => {⟨centerCell i, hcenterMem i⟩}
  let Φ : (Γ.Cell → Fin N) → ℝ := fun W => ∏ i : Fin m, evenStar Γ M σ W (a i) x
  let B : ℝ := ∏ i : Fin m, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x
  let T : Finset Γ.Cell := Finset.univ.filter fun c => ¬ Disjoint (badScope c) U
  have hnonnegΦ : ∀ W, 0 ≤ Φ W := by
    intro W
    dsimp [Φ]
    apply Finset.prod_nonneg
    intro i hi
    exact evenStar_nonneg Γ M hrow σ W (a i) x
  have hLLL : LLLInput rawP bad badScope (xL D₀ n) (R ^ 4) := by
    simpa [AnchorLLL, rawP, bad, badScope, R] using hAnchor
  have hcondResult := hCond rawP bad badScope (xL D₀ n) (R ^ 4) hLLL
  have hball (c : Γ.Cell) : (Γ.cellBall c 2).card ≤ (R : ℝ) ^ 2 := by
    simpa [R, Geom] using hGeom.balls.cellBall_card c 2
  have hTsubset : T ⊆ U.biUnion (fun c => Γ.cellBall c 2) := by
    intro c hc
    have hcnot : ¬ Disjoint (Γ.cellBall c 2) U := (Finset.mem_filter.mp hc).2
    have hmeet : ∃ u, u ∈ Γ.cellBall c 2 ∧ u ∈ U := by
      by_contra h
      push_neg at h
      apply hcnot
      exact Finset.disjoint_left.mpr (by
        intro u huBall huU
        exact h u huBall huU)
    rcases hmeet with ⟨u, huBall, huU⟩
    refine Finset.mem_biUnion.mpr ⟨u, huU, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [cellDist_comm]
    exact (Finset.mem_filter.mp huBall).2
  have hTcard : (T.card : ℝ) ≤ (m : ℝ) * (R : ℝ) ^ 2 := by
    calc
      (T.card : ℝ) ≤ ((U.biUnion fun c => Γ.cellBall c 2).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hTsubset
      _ ≤ ∑ c ∈ U, ((Γ.cellBall c 2).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := U) (t := fun c => Γ.cellBall c 2))
      _ ≤ ∑ c ∈ U, (R : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro c hc
        exact hball c
      _ = (m : ℝ) * (R : ℝ) ^ 2 := by simp [hUcard, mul_comm]
  have hTcardNat : T.card ≤ m * R ^ 2 := by
    have hTcardCast : (T.card : ℝ) ≤ ((m * R ^ 2 : ℕ) : ℝ) := by
      calc
        (T.card : ℝ) ≤ (m : ℝ) * (R : ℝ) ^ 2 := hTcard
        _ = ((m * R ^ 2 : ℕ) : ℝ) := by simp [Nat.cast_mul, Nat.cast_pow]
    exact_mod_cast hTcardCast
  have hx0 : 0 ≤ xL D₀ n := by dsimp [xL]; positivity
  have hR1 : 1 ≤ (R : ℝ) := by
    have : 1 ≤ R := by dsimp [R]; omega
    exact_mod_cast this
  have hR2 : 1 ≤ (R : ℝ) ^ 2 := by nlinarith [sq_nonneg ((R : ℝ) - 1)]
  have hxlt : xL D₀ n < 1 := by
    have hmul : 0 ≤ ((R : ℝ) ^ 2 - 1) * xL D₀ n :=
      mul_nonneg (sub_nonneg.mpr hR2) hx0
    nlinarith [hchargeSmall, hmul]
  have hbaseNonneg : 0 ≤ 1 - xL D₀ n := by linarith
  have hbaseLeOne : 1 - xL D₀ n ≤ 1 := by linarith
  have hRpowLower : (1 / 2 : ℝ) ≤ (1 - xL D₀ n) ^ (R ^ 2) := by
    have hBern := one_sub_mul_pow_lower (xL D₀ n) (R ^ 2) hx0 (by linarith [hxlt])
    calc
      (1 / 2 : ℝ) ≤ 1 - (R ^ 2 : ℝ) * xL D₀ n := by
        have hcharge := hchargeSmall
        norm_cast at hcharge
        nlinarith
      _ ≤ (1 - xL D₀ n) ^ (R ^ 2) := by simpa [Nat.cast_pow] using hBern
  have hlongPow : (1 - xL D₀ n) ^ (m * R ^ 2) ≤ (1 - xL D₀ n) ^ T.card :=
    pow_le_pow_of_le_one hbaseNonneg hbaseLeOne hTcardNat
  have hlargePow : 1 ≤ (1 - xL D₀ n) ^ (m * R ^ 2) * (2 : ℝ) ^ m := by
    calc
      1 = (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m := by rw [← mul_pow]; norm_num
      _ ≤ ((1 - xL D₀ n) ^ (R ^ 2)) ^ m * (2 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hRpowLower m) (by positivity)
      _ = (1 - xL D₀ n) ^ (m * R ^ 2) * (2 : ℝ) ^ m := by
        calc
          ((1 - xL D₀ n) ^ (R ^ 2)) ^ m * (2 : ℝ) ^ m =
              (1 - xL D₀ n) ^ ((R ^ 2) * m) * (2 : ℝ) ^ m := by rw [pow_mul]
          _ = (1 - xL D₀ n) ^ (m * R ^ 2) * (2 : ℝ) ^ m := by
            rw [Nat.mul_comm (R ^ 2) m]
  have hfactor : ((1 - xL D₀ n) ^ T.card)⁻¹ ≤ (2 : ℝ) ^ m := by
    apply (inv_le_iff_one_le_mul₀' (pow_pos (sub_pos.mpr hxlt) _)).2
    calc
      1 ≤ (1 - xL D₀ n) ^ (m * R ^ 2) * (2 : ℝ) ^ m := hlargePow
      _ ≤ (1 - xL D₀ n) ^ T.card * (2 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hlongPow (by positivity)
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (by positivity) ((M.μ (σ (Γ.key (a i).1).1)).nonneg x)
  have hBbound : ∀ ω, ∑ z : (∀ c : U, Fin N),
      (∏ c : U, (rawP c.1).w (z c)) * Φ (glue U ω z) ≤ B := by
    intro ω
    let targetFactor : Fin m → (∀ c : {c // c ∈ U}, Fin N) → ℝ := fun i z =>
      evenStar Γ M σ (glue U ω z) (a i) x
    have hscopeDisjoint : ∀ i j, i ≠ j → Disjoint (targetScope i) (targetScope j) := by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro c hci hcj
      have hci' : c = ⟨centerCell i, hcenterMem i⟩ := Finset.mem_singleton.mp hci
      have hcj' : c = ⟨centerCell j, hcenterMem j⟩ := Finset.mem_singleton.mp hcj
      apply hij
      apply hcenterInjective
      exact congrArg Subtype.val (hci'.symm.trans hcj')
    have hglueStar (i : Fin m) (z : ∀ c : {c // c ∈ U}, Fin N) :
        evenStar Γ M σ (glue U ω z) (a i) x =
          evenStar Γ M σ (Function.update ω (centerCell i)
            (z ⟨centerCell i, hcenterMem i⟩)) (a i) x := by
      apply evenStar_eq_off_far Γ M hGeom.loc σ (a i) x (U.erase (centerCell i))
      · intro c hcD
        by_cases hcU : c ∈ U
        · by_cases hcCenter : c = centerCell i
          · subst c
            simp [glue, hcU]
          · have hcErase : c ∈ U.erase (centerCell i) := Finset.mem_erase.mpr ⟨hcCenter, hcU⟩
            exact (hcD hcErase).elim
        · have hcCenter : c ≠ centerCell i := by
            intro heq
            exact hcU (heq ▸ hcenterMem i)
          simp [glue, hcU, Function.update_of_ne hcCenter
            (z ⟨centerCell i, hcenterMem i⟩) ω]
      · intro w hw
        rcases Finset.mem_image.mp (Finset.mem_of_mem_erase hw) with ⟨j, hj, hwj⟩
        have htargetNe : centerCell j ≠ centerCell i := by
          intro heq
          exact (Finset.mem_erase.mp hw).1 (hwj.symm.trans heq)
        have hroleNe : i ≠ j := by
          intro heq
          subst j
          exact htargetNe rfl
        rw [← hwj]
        exact hsep i j hroleNe
      · intro w hw
        exact (Finset.mem_erase.mp hw).1
    have hfactorDepends : ∀ i, FinProb.DependsOn (targetFactor i) (targetScope i) := by
      intro i z z' hagree
      have hz : z ⟨centerCell i, hcenterMem i⟩ = z' ⟨centerCell i, hcenterMem i⟩ :=
        hagree ⟨centerCell i, hcenterMem i⟩ (Finset.mem_singleton_self _)
      change evenStar Γ M σ (glue U ω z) (a i) x =
        evenStar Γ M σ (glue U ω z') (a i) x
      rw [hglueStar i z, hglueStar i z', hz]
    have hfactorEq := pi_expect_prod_disjoint targetLaw targetScope hscopeDisjoint targetFactor hfactorDepends
    have hfactorNonneg (i : Fin m) : 0 ≤ (FinProb.pi targetLaw).expect (targetFactor i) := by
      unfold FinProb.expect
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg ((FinProb.pi targetLaw).nonneg z)
        (evenStar_nonneg Γ M hrow σ (glue U ω z) (a i) x)
    have hfactorBound (i : Fin m) :
        (FinProb.pi targetLaw).expect (targetFactor i) ≤
          (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x := by
      let f_i : Fin N → ℝ := fun y =>
        evenStar Γ M σ (Function.update ω (centerCell i) y) (a i) x
      have hF : targetFactor i = fun z => f_i (z ⟨centerCell i, hcenterMem i⟩) := by
        funext z
        exact hglueStar i z
      have hsingle := pi_expect_singleton targetLaw ⟨centerCell i, hcenterMem i⟩ f_i
      rw [hF, hsingle]
      simpa [FinProb.expect, targetLaw, rawP, f_i] using hStar ω (a i) x
    have hfactorProduct :
        ∏ i : Fin m, (FinProb.pi targetLaw).expect (targetFactor i) ≤ B := by
      unfold B
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hfactorNonneg i
      · intro i hi
        exact hfactorBound i
    have hrawBound :
        (FinProb.pi targetLaw).expect (fun z => ∏ i : Fin m, targetFactor i z) ≤ B := by
      rw [hfactorEq]
      exact hfactorProduct
    change (FinProb.pi targetLaw).expect (fun z => Φ (glue U ω z)) ≤ B
    simpa [Φ, targetFactor] using hrawBound
  have hAnchorBound : (anchorLaw Γ M σ).expect Φ ≤ ((1 - xL D₀ n) ^ T.card)⁻¹ * B := by
    simpa [anchorLaw, rawAnchors, rawP, bad, badScope, T] using
      (hcondResult.2 U Φ hnonnegΦ B hBbound)
  calc
    (anchorLaw Γ M σ).expect Φ ≤ ((1 - xL D₀ n) ^ T.card)⁻¹ * B := hAnchorBound
    _ ≤ (2 : ℝ) ^ m * B := mul_le_mul_of_nonneg_right hfactor hBnonneg

/-- L7.1i, even loads (07:338–391): for typical tags, Lemma 3.6 with near = auxiliary distance at most five
(fraction `(q+1)^5 2^{-q}`, cap `e^{.06q}` on predictive success), comparison means `N μ_{i_{g(v)}}(x)` of
average at most `C` (typicality) and a union over labels; even column sums are `|A|/N` times the normalized
average, at most one once `N ≥ C₀ 2^n`. -/
theorem even_loads (d C : ℝ) (hd : 0 < d) (hd' : d < 1 / 8) (hC : 0 ≤ C) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι)
        (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N)),
        GeomFacts Γ → RowLaw Γ M → EvenRowCap Γ M → Typical Γ M C σ →
        (∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) → EvenMoment Γ M σ J →
        ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (J W).pr (fun f => ∃ x, 1 < evenColumn Γ M σ W f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  classical
  obtain ⟨n₀, htail⟩ := evenLoadsTail d hd
  refine ⟨max n₀ 1, 8 * (C + 1), ?_⟩
  intro n N hLarge E G X Y p κ Γ M σ J hGeom hrow hcap htyp hclock hmom
  have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hLarge.1
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hLarge.1
  have hsmall : (n : ℝ) *
      (((gQ d n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (gQ d n))⁻¹) *
        Real.exp ((6 / 100 : ℝ) * (gQ d n : ℝ)) ≤ 1 := by
    have h := htail n hn0
    convert h using 1 <;> ring
  let P : FinProb ((Γ.Cell → Fin N) × (OddRole n → Fin N)) :=
    FinProb.bind (anchorLaw Γ M σ) J
  let succ : Finset ((Γ.Cell → Fin N) × (OddRole n → Fin N)) :=
    Finset.univ.filter (fun ω => GoodPre Γ M σ ω.1)
  let usable (ω : (Γ.Cell → Fin N) × (OddRole n → Fin N)) : Prop :=
    GoodPre Γ M σ ω.1 ∧ (J ω.1).w ω.2 ≠ 0
  let Z : EvenRole n → Fin N →
      ((Γ.Cell → Fin N) × (OddRole n → Fin N)) → ℝ := fun a x ω =>
    if usable ω then (N : ℝ) * evenRow Γ M σ ω.1 ω.2 a x else 0
  let near : EvenRole n → Finset (EvenRole n) := fun a =>
    Finset.univ.filter fun b => Γ.auxDist (Γ.key b.1).2 (Γ.key a.1).2 ≤ 5
  let f : ℝ := ((gQ d n : ℝ) + 1) ^ 5 * ((2 : ℝ) ^ (gQ d n))⁻¹
  let L : ℝ := Real.exp ((6 / 100 : ℝ) * (gQ d n : ℝ))
  let avg (x : Fin N) (ω : (Γ.Cell → Fin N) × (OddRole n → Fin N)) : ℝ :=
    (Fintype.card (EvenRole n) : ℝ)⁻¹ * ∑ a, Z a x ω
  let threshold : ℝ := 16 * (C + 1)
  have hcard : Fintype.card (EvenRole n) = 2 ^ (n - 1) := hGeom.counts.even_card
  have hcardposNat : 0 < Fintype.card (EvenRole n) := by
    rw [hGeom.counts.even_card]
    exact Nat.pow_pos (by decide)
  letI : Nonempty (EvenRole n) := Fintype.card_pos_iff.mp hcardposNat
  have hcardpos : 0 < (Fintype.card (EvenRole n) : ℝ) := by
    rw [hcard]
    positivity
  have hself : ∀ a : EvenRole n, a ∈ near a := by
    intro a
    simp [near, GridGeom.auxDist]
  have hnear : ∀ a : EvenRole n, ((near a).card : ℝ) ≤ f * Fintype.card (EvenRole n) := by
    intro a
    simpa [near, f, mul_assoc, mul_left_comm, mul_comm] using hGeom.near.even_nearAux a
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hZ0 : ∀ a x ω, 0 ≤ Z a x ω := by
    intro a x ω
    by_cases hu : usable ω
    · rcases hu with ⟨hpre, hw⟩
      have hsafe := (hclock ω.1 hpre).1 ω.2 hw
      simpa [Z, usable, hpre, hw, evenRow] using
        (mul_nonneg (by positivity)
          (evenRowAt_nonneg_of_success Γ M hrow σ ω.1 a (nbrLabels ω.2 a) x (hsafe.2 a)))
    · simp [Z, hu]
  have hZL : ∀ a x ω, ω ∈ succ → Z a x ω ≤ L := by
    intro a x ω hω
    have hpre : GoodPre Γ M σ ω.1 := (Finset.mem_filter.mp hω).2
    by_cases hw : (J ω.1).w ω.2 = 0
    · simp [Z, usable, hpre, hw]
      positivity
    · have hsafe := (hclock ω.1 hpre).1 ω.2 hw
      simpa [Z, usable, hpre, hw, evenRow, L] using
        hcap σ ω.1 a (nbrLabels ω.2 a) (hsafe.2 a) x
  have hd : ∀ a : EvenRole n, ∀ x : Fin N,
      0 ≤ (N : ℝ) * (M.μ (σ (Γ.key a.1).1)).w x := by
    intro a x
    exact mul_nonneg (by positivity) ((M.μ (σ (Γ.key a.1).1)).nonneg x)
  have hmean : ∀ x : Fin N,
      (Fintype.card (EvenRole n) : ℝ)⁻¹ *
        ∑ a : EvenRole n, (N : ℝ) * (M.μ (σ (Γ.key a.1).1)).w x ≤ C := htyp
  have hjoint : ∀ (x : Fin N) (m : ℕ), m ≤ n → ∀ a : Fin m → EvenRole n,
      (∀ i j : Fin m, j < i → a i ∉ near (a j)) →
      ∑ ω ∈ succ, P.w ω * ∏ i, Z (a i) x ω ≤
        4 ^ m * ∏ i, (N : ℝ) * (M.μ (σ (Γ.key (a i).1).1)).w x := by
    intro x m hm a hsep
    have hsum :
        (∑ ω ∈ succ, P.w ω * ∏ i, Z (a i) x ω) =
          ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then
              ∑ f₀, (J W).w f₀ * ∏ i, (N : ℝ) * evenRow Γ M σ W f₀ (a i) x
             else 0) := by
      have hsumIte (g : ((Γ.Cell → Fin N) × (OddRole n → Fin N)) → ℝ) :
          (∑ ω ∈ succ, g ω) = ∑ ω, if ω ∈ succ then g ω else 0 :=
        by simpa using (Finset.sum_ite_mem_eq succ g).symm
      rw [hsumIte, Fintype.sum_prod_type]
      simp only [P, FinProb.bind]
      apply Finset.sum_congr rfl
      intro W hW
      by_cases hpre : GoodPre Γ M σ W
      · simp only [succ, Finset.mem_filter, Finset.mem_univ, true_and, hpre, ↓reduceIte]
        calc
          ∑ f₀, ((anchorLaw Γ M σ).w W * (J W).w f₀) *
              ∏ i, Z (a i) x (W, f₀) =
            ∑ f₀, (anchorLaw Γ M σ).w W *
              ((J W).w f₀ * ∏ i, (N : ℝ) * evenRow Γ M σ W f₀ (a i) x) := by
                apply Finset.sum_congr rfl
                intro f₀ hf₀
                by_cases hw : (J W).w f₀ = 0
                · simp [Z, usable, hpre, hw]
                · have hZ : ∀ i : Fin m, Z (a i) x (W, f₀) =
                    (N : ℝ) * evenRow Γ M σ W f₀ (a i) x := by
                      intro i
                      simp [Z, usable, hpre, hw]
                  simp_rw [hZ]
                  ring
          _ = (anchorLaw Γ M σ).w W *
                ∑ f₀, (J W).w f₀ *
                  ∏ i, (N : ℝ) * evenRow Γ M σ W f₀ (a i) x := by
                  rw [Finset.mul_sum]
      · simp [succ, hpre]
    rw [hsum]
    apply hmom x m hm a
    intro i j hij
    by_cases hji : j < i
    · have hnot := hsep i j hji
      have hnot' : ¬ Γ.auxDist (Γ.key (a i).1).2 (Γ.key (a j).1).2 ≤ 5 := by
        simpa [near] using hnot
      omega
    · have hij' : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
      have hnot := hsep j i hij'
      have hnot' : ¬ Γ.auxDist (Γ.key (a j).1).2 (Γ.key (a i).1).2 ≤ 5 := by
        simpa [near] using hnot
      have hdist := auxDist_comm Γ (Γ.key (a j).1).2 (Γ.key (a i).1).2
      rw [hdist] at hnot'
      omega
  have hsmall' : (n : ℝ) * f * L ≤ 1 := by
    simpa [f, L, mul_assoc] using hsmall
  have hlabels : (Fintype.card (Fin N) : ℝ) ≤ (n : ℝ) * 2 ^ n := by
    have hN : N ≤ n * 2 ^ n := hLarge.2.2
    simpa using (show (N : ℝ) ≤ (n : ℝ) * 2 ^ n by exact_mod_cast hN)
  have hunion := HypercubeRamsey.scatteredMoments_union_labels P succ
    (fun a x ω => Z a x ω) hZ0 L hL hZL near hself f hf hnear n hn1
    4 C (by norm_num) hC (fun a x => (N : ℝ) * (M.μ (σ (Γ.key a.1).1)).w x) hd hmean
    hjoint hsmall' hlabels
  have hNpos : 0 < (N : ℝ) := by
    have hlower : 0 < (8 * (C + 1)) * (2 : ℝ) ^ n := by positivity
    have hbound : (8 * (C + 1)) * (2 : ℝ) ^ n ≤ (N : ℝ) := hLarge.2.1
    exact lt_of_lt_of_le hlower hbound
  have hratio : threshold ≤ (N : ℝ) / Fintype.card (EvenRole n) := by
    have hden : (Fintype.card (EvenRole n) : ℝ) = (2 : ℝ) ^ (n - 1) := by
      rw [hcard]
      norm_cast
    rw [hden]
    have hlow : (8 * (C + 1)) * (2 : ℝ) ^ n ≤ (N : ℝ) := hLarge.2.1
    have hpow : (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ n := by
      calc
        (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ ((n - 1) + 1) := by rw [pow_succ]
        _ = (2 : ℝ) ^ n := by rw [Nat.sub_add_cancel hn1]
    have hdenpos : 0 < (2 : ℝ) ^ (n - 1) := by positivity
    apply (le_div_iff₀ hdenpos).2
    calc
      threshold * (2 : ℝ) ^ (n - 1) =
          (8 * (C + 1)) * ((2 : ℝ) ^ (n - 1) * 2) := by
            dsimp [threshold]
            ring
      _ = (8 * (C + 1)) * (2 : ℝ) ^ n := by rw [hpow]
      _ ≤ (N : ℝ) := hlow
  have havg (x : Fin N) (W : Γ.Cell → Fin N) (f₀ : OddRole n → Fin N)
      (hpre : GoodPre Γ M σ W) (hw : (J W).w f₀ ≠ 0) :
      avg x (W, f₀) = ((N : ℝ) / Fintype.card (EvenRole n)) *
        evenColumn Γ M σ W f₀ x := by
    have hsafe := (hclock W hpre).1 f₀ hw
    have hZ' : ∀ a : EvenRole n, Z a x (W, f₀) =
        (N : ℝ) * evenRow Γ M σ W f₀ a x := by
      intro a
      simp [Z, usable, hpre, hw]
    simp [avg, evenColumn, hZ', evenRow, Finset.mul_sum, div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm]
  have hmass (W : Γ.Cell → Fin N) (hpre : GoodPre Γ M σ W) :
      (J W).pr (fun f₀ => ∃ x, 1 < evenColumn Γ M σ W f₀ x) ≤
        (J W).pr (fun f₀ => ∃ x, threshold < avg x (W, f₀)) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro f₀ hf₀
    by_cases he : ∃ x, 1 < evenColumn Γ M σ W f₀ x
    · have he' := he
      obtain ⟨x, hx⟩ := he
      by_cases hw : (J W).w f₀ = 0
      · simp [he', hw]
      · have havg' := havg x W f₀ hpre hw
        have hstrict : (N : ℝ) / Fintype.card (EvenRole n) <
            ((N : ℝ) / Fintype.card (EvenRole n)) * evenColumn Γ M σ W f₀ x :=
          by simpa using mul_lt_mul_of_pos_left hx (div_pos hNpos hcardpos)
        have havgLarge : threshold < avg x (W, f₀) := by
          rw [havg']
          exact lt_of_le_of_lt hratio hstrict
        have hevent : ∃ x', threshold < avg x' (W, f₀) := ⟨x, havgLarge⟩
        simp [he', hevent]
    · simp only [he, ↓reduceIte]
      by_cases hevent : ∃ x, threshold < avg x (W, f₀)
      · simpa [hevent] using (J W).nonneg f₀
      · simp [hevent]
  have htarget :
      (∑ W, (anchorLaw Γ M σ).w W *
        (if GoodPre Γ M σ W then
          (J W).pr (fun f₀ => ∃ x, 1 < evenColumn Γ M σ W f₀ x) else 0)) ≤
      ∑ W, (anchorLaw Γ M σ).w W *
        (if GoodPre Γ M σ W then
          (J W).pr (fun f₀ => ∃ x, threshold < avg x (W, f₀)) else 0) := by
    apply Finset.sum_le_sum
    intro W hW
    by_cases hpre : GoodPre Γ M σ W
    · simp only [hpre, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (hmass W hpre) ((anchorLaw Γ M σ).nonneg W)
    · simp [hpre]
  have hUnionEq :
      (∑ ω, if ω ∈ succ ∧ ∃ x, threshold < avg x ω then P.w ω else 0) =
        ∑ W, (anchorLaw Γ M σ).w W *
          (if GoodPre Γ M σ W then
            (J W).pr (fun f₀ => ∃ x, threshold < avg x (W, f₀)) else 0) := by
    rw [Fintype.sum_prod_type]
    simp only [P, FinProb.bind, succ, Finset.mem_filter, Finset.mem_univ, true_and,
      FinProb.pr]
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hpre : GoodPre Γ M σ W
    · simp only [hpre, true_and, ↓reduceIte]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f₀ hf₀
      by_cases he : ∃ x, threshold < avg x (W, f₀) <;> simp [he]
    · simp [hpre]
  have htarget' :
      (∑ W, (anchorLaw Γ M σ).w W *
        (if GoodPre Γ M σ W then
          (J W).pr (fun f₀ => ∃ x, 1 < evenColumn Γ M σ W f₀ x) else 0)) ≤
      ∑ ω, if ω ∈ succ ∧ ∃ x, threshold < avg x ω then P.w ω else 0 := by
    rw [hUnionEq]
    exact htarget
  calc
    (∑ W, (anchorLaw Γ M σ).w W *
        (if GoodPre Γ M σ W then
          (J W).pr (fun f₀ => ∃ x, 1 < evenColumn Γ M σ W f₀ x) else 0)) ≤
      ∑ ω, if ω ∈ succ ∧ ∃ x, threshold < avg x ω then P.w ω else 0 := htarget'
    _ ≤ (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
      convert hunion using 1 <;> norm_num [avg, threshold, one_div_pow]

/-- Step 6 assembled: at tags avoiding every `B_g` (so the cell events satisfy the local-lemma input) that are
typical, any clock-sampler family gives even column sums above one with probability at most `n 2^n 4^{-n}`. -/
theorem even_stage (D₀ d C : ℝ) (hD₀ : 0 < D₀) (hD₀' : D₀ < 1 / 10) (hd : 0 < d)
    (hd' : d < D₀ / 1000) (hC : 0 ≤ C) :
    ∃ n₀ : ℕ, ∃ C₀ : ℝ, ∀ n N : ℕ, LargeAt n₀ C₀ n N →
      ∀ {E : Fin N → Fin N → Prop} {G : Colour} {X Y : Finset (Fin N)} {p κ : ℝ} (Γ : Geom d n)
        (M : Menu7 n N E G X Y d p κ) (σ : Γ.Key → M.ι)
        (J : (Γ.Cell → Fin N) → FinProb (OddRole n → Fin N)),
        GeomFacts Γ → FilterFacts Γ M → AnchorLLL Γ M D₀ σ → Typical Γ M C σ →
        (∀ W, GoodPre Γ M σ W → ClockOK Γ M σ W (J W)) →
        ∑ W, (anchorLaw Γ M σ).w W *
            (if GoodPre Γ M σ W then (J W).pr (fun f => ∃ x, 1 < evenColumn Γ M σ W f x) else 0) ≤
          (n : ℝ) * 2 ^ n * (1 / 4 : ℝ) ^ n := by
  have hd8 : d < 1 / 8 := by linarith
  obtain ⟨n₁, hint⟩ := even_anchor_integral D₀ d hD₀ hd hd'
  obtain ⟨n₂, C₂, hload⟩ := even_loads d C hd hd8 hC
  refine ⟨max n₁ n₂, C₂, ?_⟩
  intro n N hL E G X Y p κ Γ M σ J hG hF hA hty hJ
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hL.1
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) hL.1
  have hmom : EvenMoment Γ M σ J :=
    even_moment Γ M hF.row_law σ J (clock_factor Γ M hF.row_law σ J hJ)
      (hint n hn₁ Γ M σ cond_product_bound hG hF.row_law hA
        (star_cancel Γ M hF.starRef_update hF.row_law σ))
  exact hload n N ⟨hn₂, hL.2.1, hL.2.2⟩ Γ M σ J hG hF.row_law hF.evenRow_cap hty hJ hmom

end HypercubeRamsey.S07
