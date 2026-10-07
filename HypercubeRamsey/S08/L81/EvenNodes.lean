import HypercubeRamsey.S08.L81.OddNodes
import HypercubeRamsey.S03.ClockSampling
import HypercubeRamsey.Tools.ScatteredUnion
import HypercubeRamsey.S08.L81.EvenNodes_q_s08_even
import HypercubeRamsey.S08.L81.EvenNodes_q_s08_even

/-!
# Lemma 8.1, Step 12: injection, even loads and Hall

Source: `sections/08-…tex`, lines 424–454 (L8.1l).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open HypercubeRamsey.Lane_q_s08_even
open scoped BigOperators

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

set_option maxHeartbeats 1000000 in
/-- L8.1l(i) (08:425–426): on a successful prehistory every odd task is valid (the denominator and hit tests pass
and the rest of validity holds on success), so the odd rows are probability laws with atoms at most
`e^{.02 s log n}/N ≤ n^{-A}` and column sums at most `10⁻⁸`; Lemma 3.10 (`clock_sampling`, `B = 3`, `C_g = 2`)
with the predictive failures at the even vertices as forbidden predicates (scope the `n` odd neighbours, each odd
row in at most `n` scopes, product-law probability the alarm rate `≤ e^{-.02n} ≤ n^{-P}`) gives an injective odd
assignment avoiding every predictive failure with joint comparison `1 + εn ≤ 2` on at most `n^3` rows. -/
theorem clock_rows (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → (2 : ℝ) ^ D.n ≤ D.N →
      D.N ≤ D.n * 2 ^ D.n → D.SelConseq → D.PRowFacts →
      ∀ (q : D.Pre) (W : D.Anch), D.Good q → D.GoodPre q W → ∃ J, D.ClockOK q W J := by
  classical
  obtain ⟨A, P₀, nCS, ε, hε, hSampler⟩ :=
    HypercubeRamsey.clock_sampling 3 2 (by norm_num)
  have hτpos : 0 < tau8 η₀ := by rw [tau8_eq]; unfold eta8; positivity
  have hτle : tau8 η₀ ≤ (1 / 100 : ℝ) := by
    rw [tau8_eq]
    unfold eta8
    have h := min_le_right (η₀ / 2) (4 / 100 : ℝ)
    linarith
  have hτnonneg : 0 ≤ tau8 η₀ := le_of_lt hτpos
  have hceilExp : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 / 10 : ℝ) - tau8 η₀))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have hceilEv : ∀ᶠ n : ℕ in Filter.atTop,
      (2 : ℝ) ≤ (n : ℝ) ^ ((1 / 10 : ℝ) - tau8 η₀) :=
    hceilExp.eventually (Filter.eventually_ge_atTop 2)
  have hpow08 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(4 / 5 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (y := (4 / 5 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hpow09 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(9 / 10 : ℝ)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (y := (9 / 10 : ℝ)) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hsmall08 : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (-(4 / 5 : ℝ)) < Real.log 2 / 8 :=
    hpow08.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < Real.log 2 / 8))
  have hsmall09 : ∀ᶠ n : ℕ in Filter.atTop,
      |A| * (n : ℝ) ^ (-(9 / 10 : ℝ)) < Real.log 2 / 80 := by
    have hlim := hpow09.const_mul |A|
    have hthreshold : |A| * (0 : ℝ) < Real.log 2 / 80 := by
      rw [mul_zero]
      exact div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))
        (by norm_num : (0 : ℝ) < 80)
    filter_upwards [hlim.eventually (Iio_mem_nhds hthreshold)] with n hn
    simpa using hn
  have hPdecay : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ P₀ * Real.exp (-(1 / 100 : ℝ) * n))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero P₀ (1 / 100) (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hPsmall : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ P₀ * Real.exp (-(1 / 100 : ℝ) * n) < 1 :=
    hPdecay.eventually (Iio_mem_nhds (by norm_num))
  have hεsmall : ∀ᶠ n : ℕ in Filter.atTop, ε n < 1 :=
    hε.eventually (Iio_mem_nhds (by norm_num))
  have hcombined : ∀ᶠ n : ℕ in Filter.atTop,
      nCS ≤ n ∧ 2 ≤ n ∧
        2 ≤ (n : ℝ) ^ ((1 / 10 : ℝ) - tau8 η₀) ∧
        (n : ℝ) ^ (-(4 / 5 : ℝ)) < Real.log 2 / 8 ∧
        |A| * (n : ℝ) ^ (-(9 / 10 : ℝ)) < Real.log 2 / 80 ∧
        (n : ℝ) ^ P₀ * Real.exp (-(1 / 100 : ℝ) * n) < 1 ∧ ε n ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop nCS, Filter.eventually_ge_atTop 2,
      hceilEv, hsmall08, hsmall09, hPsmall, hεsmall]
      with n hnCS hn2 hceil h08 h09 hP hε
    exact ⟨hnCS, hn2, hceil, h08, h09, hP, hε.le⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hcombined
  refine ⟨n₀, ?_⟩
  intro D hn hG hNlower hNupper hSel hP q W hq hW
  have hnlarge := hn₀ D.n hn
  rcases hnlarge with ⟨hnCS, hn2, hceil, h08, h09, hPsmallD, hεD⟩
  have hnpos : 0 < (D.n : ℝ) := by exact_mod_cast (show 0 < D.n by omega)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlognNonneg : 0 ≤ Real.log D.n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ D.n by omega))
  have hlogBound : Real.log D.n ≤ 10 * (D.n : ℝ) ^ (1 / 10 : ℝ) := by
    have h := Real.log_natCast_le_rpow_div D.n (ε := (1 / 10 : ℝ)) (by norm_num)
    simpa [mul_comm] using h
  have hceilBound : (sC η₀ D.n : ℝ) ≤ (D.n : ℝ) ^ (1 / 10 : ℝ) := by
    have hround : (sC η₀ D.n : ℝ) < (D.n : ℝ) ^ tau8 η₀ + 1 := by
      dsimp [sC]
      exact Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hbase : 1 ≤ (D.n : ℝ) ^ tau8 η₀ :=
      Real.one_le_rpow (by exact_mod_cast (show 1 ≤ D.n by omega)) hτnonneg
    calc
      (sC η₀ D.n : ℝ) ≤ (D.n : ℝ) ^ tau8 η₀ + 1 := hround.le
      _ ≤ 2 * (D.n : ℝ) ^ tau8 η₀ := by nlinarith
      _ ≤ (D.n : ℝ) ^ (1 / 10 : ℝ) := by
        calc
          2 * (D.n : ℝ) ^ tau8 η₀ ≤
              (D.n : ℝ) ^ ((1 / 10 : ℝ) - tau8 η₀) * (D.n : ℝ) ^ tau8 η₀ :=
                mul_le_mul_of_nonneg_right hceil (Real.rpow_nonneg (le_of_lt hnpos) _)
          _ = (D.n : ℝ) ^ (1 / 10 : ℝ) := by
            rw [← Real.rpow_add hnpos]
            congr 1
            ring
  have hrowExponent : (2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n +
        A * Real.log D.n ≤ (D.n : ℝ) * Real.log 2 := by
    have hfirst : (2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n ≤
        (1 / 5 : ℝ) * (D.n : ℝ) ^ (1 / 5 : ℝ) := by
      calc
        (2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n ≤
        (2 / 100 : ℝ) * (D.n : ℝ) ^ (1 / 10 : ℝ) * (10 * (D.n : ℝ) ^ (1 / 10 : ℝ)) := by
              gcongr
        _ = (1 / 5 : ℝ) * ((D.n : ℝ) ^ (1 / 10 : ℝ) * (D.n : ℝ) ^ (1 / 10 : ℝ)) := by ring
        _ = (1 / 5 : ℝ) * (D.n : ℝ) ^ (1 / 5 : ℝ) := by
              congr 1
              rw [← Real.rpow_add hnpos]
              norm_num
    have hAterm : A * Real.log D.n ≤ |A| * (Real.log D.n) :=
      mul_le_mul_of_nonneg_right (le_abs_self A) hlognNonneg
    have hsmallFirst : (1 / 5 : ℝ) * (D.n : ℝ) ^ (1 / 5 : ℝ) ≤
        (1 / 40 : ℝ) * (D.n : ℝ) * Real.log 2 := by
      have hpow : (D.n : ℝ) ^ (1 / 5 : ℝ) =
          (D.n : ℝ) * (D.n : ℝ) ^ (-(4 / 5 : ℝ)) := by
        calc
          (D.n : ℝ) ^ (1 / 5 : ℝ) = (D.n : ℝ) ^ (1 + (-(4 / 5 : ℝ))) := by
            congr 1 <;> norm_num
          _ = (D.n : ℝ) ^ (1 : ℝ) * (D.n : ℝ) ^ (-(4 / 5 : ℝ)) :=
            Real.rpow_add hnpos _ _
          _ = (D.n : ℝ) * (D.n : ℝ) ^ (-(4 / 5 : ℝ)) := by rw [Real.rpow_one]
      rw [hpow]
      nlinarith [h08]
    have hsmallA : |A| * Real.log D.n ≤
        (1 / 8 : ℝ) * (D.n : ℝ) * Real.log 2 := by
      have hpow : (D.n : ℝ) ^ (1 / 10 : ℝ) =
          (D.n : ℝ) * (D.n : ℝ) ^ (-(9 / 10 : ℝ)) := by
        calc
          (D.n : ℝ) ^ (1 / 10 : ℝ) = (D.n : ℝ) ^ (1 + (-(9 / 10 : ℝ))) := by
            congr 1 <;> norm_num
          _ = (D.n : ℝ) ^ (1 : ℝ) * (D.n : ℝ) ^ (-(9 / 10 : ℝ)) :=
            Real.rpow_add hnpos _ _
          _ = (D.n : ℝ) * (D.n : ℝ) ^ (-(9 / 10 : ℝ)) := by rw [Real.rpow_one]
      calc
        |A| * Real.log D.n ≤ |A| * (10 * (D.n : ℝ) ^ (1 / 10 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogBound (abs_nonneg A)
        _ = 10 * (D.n : ℝ) * (|A| * (D.n : ℝ) ^ (-(9 / 10 : ℝ))) := by rw [hpow]; ring
        _ ≤ (1 / 8 : ℝ) * (D.n : ℝ) * Real.log 2 := by nlinarith [h09]
    calc
      (2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n + A * Real.log D.n
          ≤ (1 / 5 : ℝ) * (D.n : ℝ) ^ (1 / 5 : ℝ) +
              |A| * Real.log D.n := add_le_add (hfirst.trans_eq rfl) hAterm
      _ ≤ (1 / 40 : ℝ) * (D.n : ℝ) * Real.log 2 +
            (1 / 8 : ℝ) * (D.n : ℝ) * Real.log 2 := add_le_add hsmallFirst hsmallA
      _ ≤ (D.n : ℝ) * Real.log 2 := by nlinarith [hnpos, hlog2pos]
  have h2pow : (2 : ℝ) ^ D.n = Real.exp ((D.n : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hrowExpBound : Real.exp ((2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n) /
        (2 : ℝ) ^ D.n ≤ (D.n : ℝ) ^ (-A) := by
    rw [h2pow, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
    rw [Real.rpow_def_of_pos hnpos]
    apply Real.exp_le_exp.mpr
    nlinarith [hrowExponent]
  have hpowP : (D.n : ℝ) ^ P₀ * Real.exp (-(1 / 100 : ℝ) * D.n) < 1 := hPsmallD
  have hfailBound : Real.exp (-(2 / 100 : ℝ) * D.n) ≤ (D.n : ℝ) ^ (-P₀) := by
    have hpowPos : 0 < (D.n : ℝ) ^ P₀ := Real.rpow_pos_of_pos hnpos _
    have hexpLe : Real.exp (-(2 / 100 : ℝ) * D.n) ≤
        Real.exp (-(1 / 100 : ℝ) * D.n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hnpos]
    have hmul : (D.n : ℝ) ^ P₀ * Real.exp (-(2 / 100 : ℝ) * D.n) ≤ 1 := by
      calc
        _ ≤ (D.n : ℝ) ^ P₀ * Real.exp (-(1 / 100 : ℝ) * D.n) :=
          mul_le_mul_of_nonneg_left hexpLe (Real.rpow_nonneg (le_of_lt hnpos) _)
        _ ≤ 1 := hpowP.le
    have hdiv : Real.exp (-(2 / 100 : ℝ) * D.n) ≤ 1 / (D.n : ℝ) ^ P₀ := by
      apply (le_div_iff₀ hpowPos).2
      simpa [mul_comm] using hmul
    have hneg : (D.n : ℝ) ^ (-P₀) = ((D.n : ℝ) ^ P₀)⁻¹ :=
      Real.rpow_neg hnpos.le P₀
    simpa [hneg] using hdiv
  have hlogN : Real.log D.N ≤ 2 * (D.n : ℝ) := by
    have hNpos : 0 < (D.N : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ D.n) hNlower
    have hNupperR : (D.N : ℝ) ≤ (D.n : ℝ) * (2 : ℝ) ^ D.n := by exact_mod_cast hNupper
    have hnlog : Real.log D.n ≤ D.n := (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
    have h2log : Real.log 2 ≤ 1 := (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans (by norm_num)
    calc
      Real.log D.N ≤ Real.log ((D.n : ℝ) * (2 : ℝ) ^ D.n) := Real.log_le_log hNpos hNupperR
      _ = Real.log D.n + D.n * Real.log 2 := by
        rw [Real.log_mul hnpos.ne' (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), Real.log_pow]
      _ ≤ 2 * D.n := by nlinarith
  let sc : EvenRole D.n → Finset (OddRole D.n) := fun a => Finset.univ.image (oddNbr a)
  have hflipInj (v : CubeVertex D.n) : Function.Injective (cubeFlip v) := by
    intro i j hij
    by_contra hne
    have hi := congrFun hij i
    cases hv : v i <;> simp [cubeFlip, hne, hv] at hi
  have hoddNbrInj (a : EvenRole D.n) : Function.Injective (oddNbr a) := by
    intro i j hij
    exact hflipInj a.1 (congrArg Subtype.val hij)
  have hscCard (a : EvenRole D.n) : (sc a).card = D.n := by
    dsimp [sc]
    rw [Finset.card_image_of_injective Finset.univ (hoddNbrInj a)]
    simp
  have hcoordFlipInj (j : Fin D.n) : Function.Injective (fun v : CubeVertex D.n => cubeFlip v j) := by
    intro v w hvw
    funext k
    by_cases hkj : k = j
    · subst k
      have h := congrFun hvw j
      cases hv : v j <;> cases hw : w j <;> simp [cubeFlip, hv, hw] at h ⊢
    · have h := congrFun hvw k
      simpa [cubeFlip, hkj] using h
  have hincCard (u : OddRole D.n) :
      (Finset.univ.filter (fun a : EvenRole D.n => u ∈ sc a)).card ≤ D.n := by
    let inc : Finset (EvenRole D.n) := Finset.univ.filter fun a => u ∈ sc a
    let chooseCoord (a : inc) : Fin D.n := by
      have hmem : u ∈ sc a.1 := (Finset.mem_filter.mp a.2).2
      exact Classical.choose (Finset.mem_image.mp hmem)
    have hchoose (a : inc) : oddNbr a.1 (chooseCoord a) = u :=
      (Classical.choose_spec (Finset.mem_image.mp ((Finset.mem_filter.mp a.2).2))).2
    have hchooseInj : Function.Injective chooseCoord := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have ha := congrArg Subtype.val (hchoose a)
      have hb := congrArg Subtype.val (hchoose b)
      have ha' : cubeFlip a.1.1 (chooseCoord a) = u.1 := by simpa [oddNbr] using ha
      have hb' : cubeFlip b.1.1 (chooseCoord a) = u.1 := by simpa [oddNbr, hab] using hb
      exact hcoordFlipInj (chooseCoord a) (ha'.trans hb'.symm)
    let chooseCoordF : inc → (Finset.univ : Finset (Fin D.n)) := fun a =>
      ⟨chooseCoord a, Finset.mem_univ _⟩
    have hchooseFInj : Function.Injective chooseCoordF := by
      intro a b hab
      apply Subtype.ext
      have hab' : chooseCoord a = chooseCoord b := by
        simpa [chooseCoordF] using congrArg Subtype.val hab
      exact congrArg Subtype.val (hchooseInj hab')
    have hcard : inc.card ≤ (Finset.univ : Finset (Fin D.n)).card :=
      Finset.card_le_card_of_injective hchooseFInj
    simpa [inc] using hcard
  have hpow3 : (D.n : ℝ) ^ (3 : ℕ) = (D.n : ℝ) ^ (3 : ℝ) := by
    exact (Real.rpow_natCast (D.n : ℝ) 3).symm
  have hscope : ∀ a : EvenRole D.n,
      ((sc a).card : ℝ) ≤ (D.n : ℝ) ^ (3 : ℝ) := by
    intro a
    rw [hscCard a]
    have hncast : (1 : ℝ) ≤ D.n := by exact_mod_cast (show 1 ≤ D.n by omega)
    calc
      (D.n : ℝ) ≤ (D.n : ℝ) ^ (3 : ℕ) := by
        have hn2 : 1 ≤ (D.n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((D.n : ℝ) - 1)]
        calc
          (D.n : ℝ) = D.n * 1 := by ring
          _ ≤ D.n * (D.n : ℝ) ^ 2 := by gcongr
          _ = (D.n : ℝ) ^ 3 := by ring
      _ = (D.n : ℝ) ^ (3 : ℝ) := hpow3
  have hincidence : ∀ u : OddRole D.n,
      ((Finset.univ.filter (fun a : EvenRole D.n => u ∈ sc a)).card : ℝ) ≤ (D.n : ℝ) ^ (3 : ℝ) := by
    intro u
    have hncast : (1 : ℝ) ≤ D.n := by exact_mod_cast (show 1 ≤ D.n by omega)
    calc
      ((Finset.univ.filter (fun a : EvenRole D.n => u ∈ sc a)).card : ℝ) ≤ D.n := by exact_mod_cast hincCard u
      _ ≤ (D.n : ℝ) ^ (3 : ℕ) := by
        have hn2 : 1 ≤ (D.n : ℝ) ^ 2 := by nlinarith [sq_nonneg ((D.n : ℝ) - 1)]
        calc
          (D.n : ℝ) = D.n * 1 := by ring
          _ ≤ D.n * (D.n : ℝ) ^ 2 := by gcongr
          _ = (D.n : ℝ) ^ 3 := by ring
      _ = (D.n : ℝ) ^ (3 : ℝ) := hpow3
  have hbase (q : D.Pre) (hq : D.Good q) (g : D.KeyT) : D.BaseGates q.1.1 g := by
    by_contra hbad
    exact hq.1.1 g (Or.inl hbad)
  have hvalid (q : D.Pre) (W : D.Anch) (hq : D.Good q) (hW : D.GoodPre q W)
      (v : CubeVertex D.n) :
      D.Valid8 q W (cellOf η₀ v) := by
    let c := cellOf η₀ v
    have hsel := hSel q hq.2
    have hpres : D.PresValid q W c := by
      refine ⟨⟨hbase q hq c.1, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        exact hbase q hq u
      · intro b hb
        exact hsel.1 (c.1, b)
      · intro u
        exact hsel.1 (u.1, c.2)
      · exact (hsel.2 c).1
      · exact (hsel.2 c).2.1
      · have hnot : ¬ D.DenFail q W c := by
          intro hfail
          exact hW.1 c (Or.inl hfail)
        exact le_of_not_gt hnot
    constructor
    · exact hpres
    · have hnot : ¬ D.HitFail q W c := by
        intro hfail
        exact hW.1 c (Or.inr (Or.inl hfail))
      exact le_of_not_gt hnot
  let lab : ∀ a : OddRole D.n, Fin D.N → Fin D.N := fun _ y => y
  let row : ∀ a : OddRole D.n, FinProb (Fin D.N) := fun a =>
    ⟨fun y => D.prow q W (cellOf η₀ a.1) y,
      (hP q W (cellOf η₀ a.1)).1,
      ((hP q W (cellOf η₀ a.1)).2.2 (hvalid q W hq hW a.1)).1⟩
  have hcolumn : ∀ y : Fin D.N, ∑ a : OddRole D.n, labMarg (row a) (lab a) y ≤ (1e-8 : ℝ) := by
    intro y
    simpa [lab, row, labMarg, Ctx.oddCol] using hW.2 y
  have hAtoms : ∀ a : OddRole D.n, ∀ y : Fin D.N,
      labMarg (row a) (lab a) y ≤ (D.n : ℝ) ^ (-A) := by
    intro a y
    have hcap := ((hP q W (cellOf η₀ a.1)).2.2 (hvalid q W hq hW a.1)).2.2 y
    have hNpos : 0 < (D.N : ℝ) := lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ D.n) hNlower
    have hmass : D.prow q W (cellOf η₀ a.1) y ≤
        Real.exp ((2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n) / D.N :=
      (le_div_iff₀ hNpos).2 (by nlinarith [hcap])
    have hmass' : D.prow q W (cellOf η₀ a.1) y ≤
        Real.exp ((2 / 100 : ℝ) * (sC η₀ D.n : ℝ) * Real.log D.n) /
          (2 : ℝ) ^ D.n := by
      exact hmass.trans (div_le_div_of_nonneg_left (Real.exp_nonneg _)
        (pow_pos (by norm_num) _) hNlower)
    simpa [labMarg, lab, row] using hmass'.trans hrowExpBound
  let bad : EvenRole D.n → (OddRole D.n → Fin D.N) → Prop := fun a f =>
    D.PredFail q W a.1 (nbrLabels f a)
  let ind : EvenRole D.n → (OddRole D.n → Fin D.N) → ℝ := fun a f =>
    if bad a f then 1 else 0
  have hdepends : ∀ a : EvenRole D.n,
      FinProb.DependsOn (bad a) (sc a) := by
    intro a f g hag
    have hlabels : nbrLabels f a = nbrLabels g a := by
      funext j
      exact hag (oddNbr a j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
    simp [bad, hlabels]
  have hindepends : ∀ a : EvenRole D.n,
      FinProb.DependsOn (ind a) (sc a) := by
    intro a f g hag
    have h := hdepends a f g hag
    simp [ind, h]
  have hNposNat : 0 < D.N := by
    have hNposR : (0 : ℝ) < D.N := lt_of_lt_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ D.n) hNlower
    exact Nat.cast_pos.mp hNposR
  let defaultOut : Fin D.N := ⟨0, by omega⟩
  have hAlarmProb : ∀ a : EvenRole D.n,
      (FinProb.pi row).pr (bad a) = D.alarmRate q W a.1 := by
    intro a
    let S := {u : OddRole D.n // u ∈ sc a}
    let e : Fin D.n ≃ S :=
      { toFun := fun j => ⟨oddNbr a j,
          Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
        invFun := fun u => Classical.choose (Finset.mem_image.mp u.2)
        left_inv := by
          intro j
          apply hoddNbrInj a
          exact (Classical.choose_spec
            (Finset.mem_image.mp (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))).2
        right_inv := by
          intro u
          apply Subtype.ext
          exact (Classical.choose_spec (Finset.mem_image.mp u.2)).2 }
    let E : (Fin D.n → Fin D.N) ≃ (S → Fin D.N) :=
      { toFun := fun y u => y (e.symm u)
        invFun := fun ψ j => ψ (e j)
        left_inv := by intro y; funext j; simp
        right_inv := by intro ψ; funext u; simp }
    let patch : (S → Fin D.N) → (OddRole D.n → Fin D.N) := fun ψ =>
      (Equiv.piEquivPiSubtypeProd (fun u : OddRole D.n => u ∈ sc a)
        (fun _ => Fin D.N)).symm (ψ, fun _ => defaultOut)
    let full : (S → Fin D.N) → (OddRole D.n → Fin D.N) := fun ψ u =>
      if hu : u ∈ sc a then ψ ⟨u, hu⟩ else defaultOut
    have hpatch (ψ : S → Fin D.N) :
        ∀ u (hu : u ∈ sc a), patch ψ u = full ψ u := by
      intro u hu
      simp [patch, full, Equiv.piEquivPiSubtypeProd_symm_apply, hu]
    have hprExp : (FinProb.pi row).pr (bad a) = (FinProb.pi row).expect (ind a) := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hbad : bad a f <;> simp [ind, hbad]
    rw [hprExp]
    rw [FinProb.pi_expect_depends row (sc a) (ind a) (fun _ => defaultOut) (hindepends a)]
    unfold FinProb.expect Ctx.alarmRate
    change (∑ ψ : S → Fin D.N,
        (∏ u : S, (row u.1).w (ψ u)) * ind a (patch ψ)) =
      ∑ y : Fin D.n → Fin D.N,
        (∏ j, D.prow q W (cellOf η₀ (cubeFlip a.1 j)) (y j)) *
          (if D.PredFail q W a.1 y then 1 else 0)
    rw [← Equiv.sum_comp E (fun ψ =>
      (∏ u : S, (row u.1).w (ψ u)) * ind a (patch ψ))]
    apply Finset.sum_congr rfl
    intro y hy
    have hprod : ∏ u : S, (row u.1).w ((E y) u) =
        ∏ j : Fin D.n, (row (oddNbr a j)).w (y j) := by
      calc
        ∏ u : S, (row u.1).w ((E y) u) =
            ∏ j : Fin D.n, (row (e j).1).w ((E y) (e j)) := by
              symm
              exact Fintype.prod_equiv e _ _ (by intro j; rfl)
        _ = ∏ j : Fin D.n, (row (e j).1).w (y j) := by
              apply Finset.prod_congr rfl
              intro j hj
              rw [show (E y) (e j) = y j by simp [E]]
        _ = ∏ j : Fin D.n, (row (oddNbr a j)).w (y j) := by
              apply Finset.prod_congr rfl
              intro j hj
              rfl
    have hlabels : ∀ j : Fin D.n, full (E y) (oddNbr a j) = y j := by
      intro j
      have hm : oddNbr a j ∈ sc a := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have he : e j = ⟨oddNbr a j, hm⟩ := rfl
      simp only [full, dif_pos hm]
      change y (e.symm ⟨oddNbr a j, hm⟩) = y j
      rw [← he, e.symm_apply_apply]
    have hind : ind a (patch (E y)) =
        (if D.PredFail q W a.1 y then 1 else 0) := by
      have hEq := hindepends a (patch (E y)) (full (E y)) (hpatch (E y))
      have hbad : bad a (full (E y)) = D.PredFail q W a.1 y := by
        simp only [bad]
        congr 1
        funext j
        exact hlabels j
      simp only [ind] at hEq
      rw [hbad] at hEq
      simpa [ind] using hEq
    change (∏ u : S, (row u.1).w ((E y) u)) *
        ind a (patch (E y)) =
      (∏ j : Fin D.n, D.prow q W (cellOf η₀ (cubeFlip a.1 j)) (y j)) *
        (if D.PredFail q W a.1 y then 1 else 0)
    rw [hprod, hind]
    rfl
  have hfail : ∀ a : EvenRole D.n,
      (FinProb.pi row).pr (bad a) ≤ (D.n : ℝ) ^ (-P₀) := by
    intro a
    rw [hAlarmProb a]
    have hnotAlarm : ¬ D.Alarm q W (cellOf η₀ a.1) := by
      intro ha
      exact hW.1 _ (Or.inr (Or.inr ha))
    have hrate : D.alarmRate q W a.1 ≤ Real.exp (-(2 / 100 : ℝ) * D.n) := by
      by_contra h
      exact hnotAlarm ⟨a, rfl, lt_of_not_ge h⟩
    exact hrate.trans hfailBound
  have hlogcond : Real.log D.N ≤ 2 * (D.n : ℝ) := hlogN
  have hScopeBound : ∀ a : EvenRole D.n,
      ((sc a).card : ℝ) ≤ (D.n : ℝ) ^ (3 : ℝ) := hscope
  have hIncidenceBound : ∀ u : OddRole D.n,
      ((Finset.univ.filter (fun a : EvenRole D.n => u ∈ sc a)).card : ℝ) ≤ (D.n : ℝ) ^ (3 : ℝ) := hincidence
  have hsampling := hSampler D.n hnCS D.N hlogcond lab row bad sc hcolumn hAtoms hdepends hScopeBound hIncidenceBound hfail
  rcases hsampling with ⟨J, hJsupp, hJjoint⟩
  refine ⟨J, ?_, ?_⟩
  · intro f hf
    have hs := hJsupp f hf
    refine ⟨?_, ?_⟩
    · simpa [lab] using hs.1
    · intro a
      simpa [bad] using hs.2 a
  · intro S o hS
    have hSReal : (S.card : ℝ) ≤ (D.n : ℝ) ^ (3 : ℝ) := by
      rw [← hpow3]
      exact hS
    have hbound := hJjoint S o hSReal
    have hprodNonneg : 0 ≤ ∏ u ∈ S, (row u).w (o u) :=
      Finset.prod_nonneg fun u hu => (row u).nonneg (o u)
    calc
      J.pr (fun f => ∀ u ∈ S, f u = o u) ≤
          (1 + ε D.n) * ∏ u ∈ S, (row u).w (o u) := hbound
      _ ≤ 2 * ∏ u ∈ S, (row u).w (o u) := by
          exact mul_le_mul_of_nonneg_right (by linarith [hεD]) hprodNonneg
      _ = 2 * ∏ u ∈ S, D.prow q W (cellOf η₀ u.1) (o u) := by rfl

/-- L8.1l(ii) (08:427–432): on predictive success `M_v > 0`, so the posterior row is a probability law; a label in its
support has `F_x(y) ≠ 0`, so every neighbouring odd row, recomputed with `v`'s anchor equal to `x`, is positive at
its label; `v`'s cell is a padded even neighbour of each neighbour's cell (edge cover), so the label hits `x`. -/
theorem evenRow_law (D : Ctx η₀ β p h) (hG : GridFacts η₀ D.n) (hP : D.PRowFacts) : D.EvenRowLaw := by
  intro q W f a hgood
  let y' := nbrLabels f a
  have hrow_nonneg : ∀ x, 0 ≤ D.evenRowAt q W a y' x := by
    intro x
    have hlik : 0 ≤ D.starLik q W a.1 x y' := by
      unfold Ctx.starLik
      exact Finset.prod_nonneg fun j _ =>
        (hP q (Function.update W (cellOf η₀ a.1) x) (cellOf η₀ (cubeFlip a.1 j))).1 (y' j)
    have hmarg_nonneg : 0 ≤ D.starMarg q W a.1 y' := by
      unfold Ctx.starMarg
      exact Finset.sum_nonneg fun z _ => mul_nonneg ((D.Usel q (cellOf η₀ a.1)).nonneg z)
        (by
          unfold Ctx.starLik
          exact Finset.prod_nonneg fun j _ => (hP q (Function.update W (cellOf η₀ a.1) z)
            (cellOf η₀ (cubeFlip a.1 j))).1 (y' j))
    have hmarg_ne : D.starMarg q W a.1 y' ≠ 0 := by
      intro hz
      exact hgood (Or.inl hz)
    have hmarg_pos : 0 < D.starMarg q W a.1 y' := lt_of_le_of_ne hmarg_nonneg (Ne.symm hmarg_ne)
    exact div_nonneg (mul_nonneg hlik ((D.Usel q (cellOf η₀ a.1)).nonneg x)) hmarg_pos.le
  have hsumlik : ∑ x : Fin D.N, D.starLik q W a.1 x y' * (D.Usel q (cellOf η₀ a.1)).w x =
      D.starMarg q W a.1 y' := by
    unfold Ctx.starMarg
    apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm]
  refine ⟨hrow_nonneg, ?_, ?_⟩
  · have hmarg_ne : D.starMarg q W a.1 y' ≠ 0 := by
      intro hz
      exact hgood (Or.inl hz)
    calc
      ∑ x : Fin D.N, D.evenRowAt q W a y' x =
          (∑ x : Fin D.N, D.starLik q W a.1 x y' * (D.Usel q (cellOf η₀ a.1)).w x) /
            D.starMarg q W a.1 y' := by
              simp only [Ctx.evenRowAt, Finset.sum_div]
      _ = 1 := by rw [hsumlik, div_self hmarg_ne]
  · intro x hx b hadj
    have hmarg_ne : D.starMarg q W a.1 y' ≠ 0 := by
      intro hz
      exact hgood (Or.inl hz)
    have hlik_ne : D.starLik q W a.1 x y' ≠ 0 := by
      intro hz
      apply hx
      simp [Ctx.evenRow, Ctx.evenRowAt, y', hz]
    have hflip : ∃ j : Fin D.n, b.1 = cubeFlip a.1 j := by
      change _root_.hammingDist a.1 b.1 = 1 at hadj
      classical
      unfold _root_.hammingDist at hadj
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hadj
      refine ⟨j, ?_⟩
      funext i
      by_cases hij : i = j
      · subst i
        have hdiff : a.1 j ≠ b.1 j := by
          have hmem : j ∈ Finset.univ.filter (fun i : Fin D.n => a.1 i ≠ b.1 i) := by
            rw [hj]
            simp
          exact (Finset.mem_filter.mp hmem).2
        cases ha : a.1 j <;> cases hb : b.1 j <;> simp_all [cubeFlip]
      · have hnot : i ∉ Finset.univ.filter (fun i : Fin D.n => a.1 i ≠ b.1 i) := by
          rw [hj]
          simp [hij]
        have heq : a.1 i = b.1 i := by
          by_contra hne
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        change b.1 i = Function.update a.1 j (!a.1 j) i
        rw [Function.update_of_ne hij]
        exact heq.symm
    obtain ⟨j, hbj⟩ := hflip
    have hrow_ne : D.prow q (Function.update W (cellOf η₀ a.1) x)
        (cellOf η₀ (cubeFlip a.1 j)) (y' j) ≠ 0 := by
      intro hz
      apply hlik_ne
      unfold Ctx.starLik
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    have hAdjBA : (cube D.n).Adj b.1 a.1 := by
      simpa [hbj] using (cubeFlip_adj a.1 j).symm
    have hPad : PadNbr (cellOf η₀ b.1) (cellOf η₀ a.1) := hG.edge b.1 a.1 hAdjBA
    have hhit := (hP q (Function.update W (cellOf η₀ a.1) x)
      (cellOf η₀ (cubeFlip a.1 j))).2.1 (y' j) hrow_ne (cellOf η₀ a.1) (by simpa [hbj] using hPad)
    have hodd : oddNbr a j = b := by
      apply Subtype.ext
      change cubeFlip a.1 j = b.1
      exact hbj.symm
    simpa [y', nbrLabels, hodd, Function.update_self] using hhit

/-- L8.1l(iii) (08:433–437): on success the selected tag passes its cutoffs, so
`N max U_v ≤ e^{n^γ + log 2 + n^{2τ}}/(1-Δ) = e^{o(n)}`; with `F_x ≤ e^{.03n} Q_v` and `M_v ≥ e^{-.04n} Q_v`,
`N max w_v ≤ e^{.1n}` for large `n`. -/
theorem evenRow_cap (hη₀ : 0 < η₀) (hγ₁ : γ < 1) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.StarLikBound → D.SelConseq → D.EvenRowCap := by
  have htau_pos : 0 < tau8 η₀ := by
    rw [tau8_eq]
    unfold eta8
    positivity
  have htau_le : tau8 η₀ ≤ (1 / 100 : ℝ) := by
    rw [tau8_eq]
    unfold eta8
    have hmin := min_le_right (η₀ / 2) (4 / 100 : ℝ)
    linarith
  have hgammaT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (γ - 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := 1 - γ) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    have heq : (fun n : ℕ => (n : ℝ) ^ (γ - 1)) =
        fun n : ℕ => (n : ℝ) ^ (-(1 - γ)) := by
      funext n
      congr 1
      ring
    rw [heq]
    exact h
  have htauT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * tau8 η₀ - 1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (y := 1 - 2 * tau8 η₀) (by linarith)).comp
      tendsto_natCast_atTop_atTop
    have heq : (fun n : ℕ => (n : ℝ) ^ (2 * tau8 η₀ - 1)) =
        fun n : ℕ => (n : ℝ) ^ (-(1 - 2 * tau8 η₀)) := by
      funext n
      congr 1
      ring
    rw [heq]
    exact h
  have hpPowT : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (p / 2)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < p / 2)).comp tendsto_natCast_atTop_atTop
  have hdeltaT : Filter.Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) ^ (p / 2))))
      Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hpPowT)
  have hgammaEv : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (γ - 1) < (1 / 100 : ℝ) :=
    hgammaT.eventually (Iio_mem_nhds (by norm_num))
  have htauEv : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (2 * tau8 η₀ - 1) < (1 / 100 : ℝ) :=
    htauT.eventually (Iio_mem_nhds (by norm_num))
  have hlogEv : ∀ᶠ n : ℕ in Filter.atTop, 2 * Real.log 2 ≤ (1 / 100 : ℝ) * (n : ℝ) := by
    have hevent := tendsto_natCast_atTop_atTop.eventually
      (Filter.eventually_ge_atTop (200 * Real.log 2))
    filter_upwards [hevent] with n hn
    nlinarith
  have hdeltaEv : ∀ᶠ n : ℕ in Filter.atTop, Real.exp (-((n : ℝ) ^ (p / 2))) ≤ (1 / 2 : ℝ) := by
    filter_upwards [hdeltaT.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
    exact hn.le
  have hlargeEv : ∀ᶠ n : ℕ in Filter.atTop,
      2 ≤ n ∧ (n : ℝ) ^ (γ - 1) < 1 / 100 ∧
      (n : ℝ) ^ (2 * tau8 η₀ - 1) < 1 / 100 ∧
      2 * Real.log 2 ≤ (1 / 100 : ℝ) * n ∧
      Real.exp (-((n : ℝ) ^ (p / 2))) ≤ 1 / 2 := by
    filter_upwards [Filter.eventually_ge_atTop 2, hgammaEv, htauEv, hlogEv, hdeltaEv]
      with n hn hγ hτ hlog hδ
    exact ⟨hn, hγ, hτ, hlog, hδ⟩
  obtain ⟨n₀, hlarge⟩ := Filter.eventually_atTop.mp hlargeEv
  refine ⟨n₀, ?_⟩
  intro D hn X Y R hStd hG hSLB hSel
  intro q W a y hq hpred x
  have hnlarge := hlarge D.n hn
  rcases hnlarge with ⟨hn2, hγsmall, hτsmall, hlogsmall, hdelta⟩
  have hnpos : 0 < (D.n : ℝ) := by exact_mod_cast (by omega : 0 < D.n)
  have hγeq : (D.n : ℝ) ^ (γ - 1) = (D.n : ℝ) ^ γ / D.n := by
    rw [Real.rpow_sub_one (ne_of_gt hnpos)]
  have hγbound : (D.n : ℝ) ^ γ ≤ (1 / 100 : ℝ) * D.n := by
    rw [hγeq] at hγsmall
    exact (div_lt_iff₀ hnpos).mp hγsmall |>.le
  have hτeq : (D.n : ℝ) ^ (2 * tau8 η₀ - 1) =
      (D.n : ℝ) ^ (2 * tau8 η₀) / D.n := by
    rw [Real.rpow_sub_one (ne_of_gt hnpos)]
  have hτbound : (D.n : ℝ) ^ (2 * tau8 η₀) ≤ (1 / 100 : ℝ) * D.n := by
    rw [hτeq] at hτsmall
    exact (div_lt_iff₀ hnpos).mp hτsmall |>.le
  have hExponent : (D.n : ℝ) ^ γ + (D.n : ℝ) ^ (2 * tau8 η₀) +
      2 * Real.log 2 ≤ (3 / 100 : ℝ) * D.n := by
    nlinarith [hγbound, hτbound, hlogsmall]
  have hDelta : D.Δ ≤ 1 / 2 := by simpa [Ctx.Δ] using hdelta
  have hDeltaDen : 0 < 1 - D.Δ := by linarith
  let hTheta : D.Hist := q.1.1
  let c := cellOf η₀ a.1
  have hnotBad : ¬ D.HBad hTheta c.1 := by
    change ¬ D.HBad q.1.1 c.1
    exact hq.1.1 c.1
  have hBase : D.BaseGates hTheta c.1 := by
    by_contra hfail
    exact hnotBad (Or.inl hfail)
  have hCon := hSel q hq.2
  obtain ⟨ℓ, hsel⟩ := Option.isSome_iff_exists.mp (hCon.1 c)
  let i := q.2.1.1 c.1 ℓ
  have htiltPos : 0 < (D.tilt hTheta c.1).w i := by
    change 0 < (D.tilt q.1.1 c.1).w (q.2.1.1 c.1 ℓ)
    exact hq.1.2 c.1 ℓ
  have hAGPos : 0 < D.AG c.1 := by unfold Ctx.AG; positivity
  have hZGPos : 0 < D.ZG hTheta c.1 :=
    lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) hAGPos) hBase.2.1.1
  have hZGne : D.ZG hTheta c.1 ≠ 0 := ne_of_gt hZGPos
  have hsumZGne : (∑ j, D.tiltW hTheta c.1 j) ≠ 0 := by
    simpa [Ctx.ZG] using hZGne
  have htiltFormula : (D.tilt hTheta c.1).w i = D.tiltW hTheta c.1 i / D.ZG hTheta c.1 := by
    change (if (∑ j, D.tiltW hTheta c.1 j) = 0 then D.tagLaw.w i else
      D.tiltW hTheta c.1 i / (∑ j, D.tiltW hTheta c.1 j)) = _
    rw [if_neg hsumZGne]
    rfl
  have htiltWPos : 0 < D.tiltW hTheta c.1 i := by
    rw [htiltFormula] at htiltPos
    exact (div_pos_iff_of_pos_right hZGPos).mp htiltPos
  have htag : D.selTag q c = some i := by simp [Ctx.selTag, i, hsel]
  have hUsel : D.Usel q c = D.anchorU hTheta c.1 i := by
    change D.Usel q c = D.anchorU q.1.1 c.1 i
    simp [Ctx.Usel, Ctx.selTag, i, hsel]
  have hGateOpen : D.GateOpen hTheta c.1 i := by
    by_contra hfail
    have hzero : D.tiltW hTheta c.1 i = 0 := by simp [Ctx.tiltW, hfail]
    exact (ne_of_gt htiltWPos) hzero
  have hpostPos : 0 < D.postW (hTheta c.1) i := by
    by_contra hnonpos
    have hpostZero : D.postW (hTheta c.1) i = 0 :=
      le_antisymm (le_of_not_gt hnonpos) (D.postW_nonneg _ _)
    have hzero : D.tiltW hTheta c.1 i = 0 := by
      simp [Ctx.tiltW, hGateOpen, hpostZero]
    exact (ne_of_gt htiltWPos) hzero
  have hLambda : 0 < D.M.Λ i := by
    by_contra hnonpos
    have hzero : D.M.Λ i = 0 := le_antisymm (le_of_not_gt hnonpos) (D.M.Λ_nonneg i)
    have hG1 := hBase.1 i
    rw [hzero] at hG1
    have h := hpostPos
    have : D.postW (hTheta c.1) i ≤ 0 := by
      simpa using hG1
    linarith
  have hmuWidth := (hStd.laws i hLambda).2.2.1
  have hNPos : 0 < (D.N : ℝ) := by exact_mod_cast hStd.size.1
  have hmuCap : (D.N : ℝ) * (D.M.μ i).w x ≤
      Real.exp ((D.n : ℝ) ^ γ + Real.log 2) := by
    calc
      (D.N : ℝ) * (D.M.μ i).w x ≤
          (D.N : ℝ) * (Real.exp ((D.n : ℝ) ^ γ + Real.log 2) / D.N) :=
            mul_le_mul_of_nonneg_left (hmuWidth x) (Nat.cast_nonneg _)
      _ = Real.exp ((D.n : ℝ) ^ γ + Real.log 2) := by field_simp [ne_of_gt hNPos]
  have hDplusLower : (1 - D.Δ) * D.cut ≤ D.dPlus hTheta c.1 i := by
    calc
      (1 - D.Δ) * D.cut ≤ (1 - D.Δ) * D.dMinus hTheta c.1 i :=
        mul_le_mul_of_nonneg_left hGateOpen.1 hDeltaDen.le
      _ ≤ D.dPlus hTheta c.1 i := hGateOpen.2
  have hDplusPos : 0 < D.dPlus hTheta c.1 i := by
    apply lt_of_lt_of_le _ hDplusLower
    exact mul_pos hDeltaDen (Real.exp_pos _)
  have hDplusSum :
      (∑ z, (D.M.μ i).w z * if D.ownHit hTheta c.1 z then 1 else 0) =
        D.dPlus hTheta c.1 i := rfl
  have hsumAnchorPos :
      0 < ∑ z, (D.M.μ i).w z * if D.ownHit hTheta c.1 z then 1 else 0 := by
    rw [hDplusSum]
    exact hDplusPos
  have hanchorFormula : (D.anchorU hTheta c.1 i).w x =
      (D.M.μ i).w x * (if D.ownHit hTheta c.1 x then 1 else 0) / D.dPlus hTheta c.1 i := by
    unfold Ctx.anchorU normOr
    change (if (∑ z, (D.M.μ i).w z * (if D.ownHit hTheta c.1 z then 1 else 0)) = 0 then
        (D.M.μ i).w x else
        ((D.M.μ i).w x * (if D.ownHit hTheta c.1 x then 1 else 0) /
          ∑ z, (D.M.μ i).w z * (if D.ownHit hTheta c.1 z then 1 else 0))) = _
    rw [if_neg (ne_of_gt hsumAnchorPos), hDplusSum]
  have hUraw : (D.anchorU hTheta c.1 i).w x ≤ (D.M.μ i).w x / D.dPlus hTheta c.1 i := by
    rw [hanchorFormula]
    by_cases hhit : D.ownHit hTheta c.1 x
    · simp [hhit]
    · simp [hhit]
      exact div_nonneg ((D.M.μ i).nonneg x) hDplusPos.le
  have hUcap : (D.N : ℝ) * (D.Usel q c).w x ≤ Real.exp ((3 / 100 : ℝ) * D.n) := by
    rw [hUsel]
    let E₀ : ℝ := (D.n : ℝ) ^ γ + Real.log 2 + (D.n : ℝ) ^ (2 * tau8 η₀)
    calc
      (D.N : ℝ) * (D.anchorU hTheta c.1 i).w x ≤
          (D.N : ℝ) * ((D.M.μ i).w x / D.dPlus hTheta c.1 i) :=
            mul_le_mul_of_nonneg_left hUraw (Nat.cast_nonneg _)
      _ = ((D.N : ℝ) * (D.M.μ i).w x) / D.dPlus hTheta c.1 i := by ring
      _ ≤ Real.exp ((D.n : ℝ) ^ γ + Real.log 2) / D.dPlus hTheta c.1 i :=
            div_le_div_of_nonneg_right hmuCap (le_of_lt hDplusPos)
      _ ≤ Real.exp ((D.n : ℝ) ^ γ + Real.log 2) / ((1 - D.Δ) * D.cut) :=
            div_le_div_of_nonneg_left (Real.exp_nonneg _) (mul_pos hDeltaDen (Real.exp_pos _)) hDplusLower
      _ = Real.exp E₀ / (1 - D.Δ) := by
            rw [Ctx.cut]
            let A₀ : ℝ := (D.n : ℝ) ^ γ + Real.log 2
            let B₀ : ℝ := (D.n : ℝ) ^ (2 * tau8 η₀)
            have hAB : A₀ + B₀ = E₀ := rfl
            calc
              Real.exp A₀ / ((1 - D.Δ) * Real.exp (-B₀)) =
                  (Real.exp A₀ * Real.exp B₀) / (1 - D.Δ) := by
                      rw [Real.exp_neg]
                      field_simp [ne_of_gt hDeltaDen, (Real.exp_pos B₀).ne'] <;> ring
              _ = Real.exp (A₀ + B₀) / (1 - D.Δ) :=
                congrArg (fun z : ℝ => z / (1 - D.Δ)) (Real.exp_add A₀ B₀).symm
              _ = Real.exp E₀ / (1 - D.Δ) :=
                congrArg (fun z : ℝ => Real.exp z / (1 - D.Δ)) hAB
      _ ≤ 2 * Real.exp E₀ := by
            apply (div_le_iff₀ hDeltaDen).2
            calc
              Real.exp E₀ = Real.exp E₀ * 1 := by ring
              _ ≤ Real.exp E₀ * (2 * (1 - D.Δ)) :=
                mul_le_mul_of_nonneg_left (by linarith [hDelta]) (Real.exp_nonneg E₀)
              _ = 2 * Real.exp E₀ * (1 - D.Δ) := by ring
      _ = Real.exp (E₀ + Real.log 2) := by
            have hlog2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
            calc
              2 * Real.exp E₀ = Real.exp (Real.log 2) * Real.exp E₀ := by rw [hlog2]
              _ = Real.exp (Real.log 2 + E₀) := (Real.exp_add _ _).symm
              _ = Real.exp (E₀ + Real.log 2) := congrArg Real.exp (add_comm (Real.log 2) E₀)
      _ ≤ Real.exp ((3 / 100 : ℝ) * D.n) := by
            apply Real.exp_le_exp.mpr
            have hExp₀ : E₀ + Real.log 2 ≤ (3 / 100 : ℝ) * D.n := by
              dsimp [E₀]
              linarith [hExponent]
            exact hExp₀
  have havgNN (Q : FinProb D.Tup) (z : Fin D.N) :
      0 ≤ averageCoordinateMarginal Q z := by
    unfold averageCoordinateMarginal
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_nonneg fun j _ => pr_nonneg Q (fun θ => θ j = z)
  have hlightNN (Q : FinProb D.Tup) : 0 ≤ D.lightMass Q := by
    classical
    unfold Ctx.lightMass
    apply Finset.sum_nonneg
    intro z hz
    by_cases hh : z ∈ heavyCoordinateSet Q D.heavyB
    · simp [hh]
    · simpa [hh] using havgNN Q z
  have hp0wNN (Θ : D.Hist) (P : D.Pos) (c' : D.CellT) (π : D.Pres c'.1) (z : Fin D.N) :
      0 ≤ D.p0w Θ P c' π z := by
    classical
    by_cases hlight : D.lightMass (D.selPost Θ P c' π) = 0
    · simp [Ctx.p0w, hlight]
    · by_cases hheavy : z ∈ heavyCoordinateSet (D.selPost Θ P c' π) D.heavyB
      · simp [Ctx.p0w, hlight, hheavy]
      · simpa [Ctx.p0w, hlight, hheavy] using
          div_nonneg (havgNN (D.selPost Θ P c' π) z) (hlightNN _)
  have hp0NN (q' : D.Pre) (W' : D.Anch) (c' : D.CellT) (z : Fin D.N) :
      0 ≤ D.p0 q' W' c' z := by
    classical
    by_cases hv : D.PresValid q' W' c'
    · simpa [Ctx.p0, hv] using hp0wNN q'.1.1 q'.1.2 c' (D.presOf q' W' c') z
    · simp [Ctx.p0, hv]
  have hprowNN (q' : D.Pre) (W' : D.Anch) (c' : D.CellT) (z : Fin D.N) :
      0 ≤ D.prow q' W' c' z := by
    classical
    by_cases hv : D.Valid8 q' W' c'
    · unfold Ctx.prow
      rw [if_pos hv]
      exact div_nonneg
        (mul_nonneg (hp0NN q' W' c' z) (by positivity))
        (Finset.sum_nonneg fun t _ => mul_nonneg (hp0NN q' W' c' t) (by positivity))
    · simp [Ctx.prow, hv]
  have hMargNonneg : 0 ≤ D.starMarg q W a.1 y := by
    unfold Ctx.starMarg
    exact Finset.sum_nonneg fun z _ => mul_nonneg
      ((D.Usel q (cellOf η₀ a.1)).nonneg z)
      (by
        unfold Ctx.starLik
        exact Finset.prod_nonneg fun j _ =>
          hprowNN q (Function.update W (cellOf η₀ a.1) z) (cellOf η₀ (cubeFlip a.1 j)) (y j))
  have hMargNe : D.starMarg q W a.1 y ≠ 0 := by
    intro hzero
    exact hpred (Or.inl hzero)
  have hMargPos : 0 < D.starMarg q W a.1 y := lt_of_le_of_ne hMargNonneg (Ne.symm hMargNe)
  have hLikNonneg : 0 ≤ D.starLik q W a.1 x y := by
    unfold Ctx.starLik
    exact Finset.prod_nonneg fun j _ =>
      hprowNN q (Function.update W (cellOf η₀ a.1) x) (cellOf η₀ (cubeFlip a.1 j)) (y j)
  have hRefNonneg : 0 ≤ D.starRef q W a.1 y := by
    have hSL := hSLB q W a.1 x y
    have he := Real.exp_pos ((3 / 100 : ℝ) * D.n)
    by_contra hneg
    have hqneg : D.starRef q W a.1 y < 0 := lt_of_not_ge hneg
    have hlt : Real.exp ((3 / 100 : ℝ) * D.n) * D.starRef q W a.1 y < 0 := mul_neg_of_pos_of_neg he hqneg
    linarith [hLikNonneg, hSL]
  have hRefLe : D.starRef q W a.1 y / D.starMarg q W a.1 y ≤ Real.exp ((4 / 100 : ℝ) * D.n) := by
    have hnotlt : ¬ D.starMarg q W a.1 y <
        Real.exp (-(4 / 100 : ℝ) * D.n) * D.starRef q W a.1 y := by
      intro hlt
      exact hpred (Or.inr hlt)
    have hscale : D.starRef q W a.1 y ≤
        Real.exp ((4 / 100 : ℝ) * D.n) * D.starMarg q W a.1 y := by
      have hle : Real.exp (-(4 / 100 : ℝ) * D.n) * D.starRef q W a.1 y ≤ D.starMarg q W a.1 y := le_of_not_gt hnotlt
      have := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg ((4 / 100 : ℝ) * D.n))
      have hexp : Real.exp ((4 / 100 : ℝ) * D.n) * Real.exp (-(4 / 100 : ℝ) * D.n) = 1 := by
        rw [← Real.exp_add]
        simp
      calc
        D.starRef q W a.1 y = 1 * D.starRef q W a.1 y := by ring
        _ = (Real.exp ((4 / 100 : ℝ) * D.n) * Real.exp (-(4 / 100 : ℝ) * D.n)) *
              D.starRef q W a.1 y := by rw [hexp]
        _ ≤ Real.exp ((4 / 100 : ℝ) * D.n) * D.starMarg q W a.1 y := by
              nlinarith [hRefNonneg, hle, Real.exp_pos ((4 / 100 : ℝ) * D.n)]
    exact (div_le_iff₀ hMargPos).2 hscale
  have hRow : (D.N : ℝ) * D.evenRowAt q W a y x ≤ Real.exp ((1 / 10 : ℝ) * D.n) := by
    have hSL := hSLB q W a.1 x y
    have hFoverM : D.starLik q W a.1 x y / D.starMarg q W a.1 y ≤
        Real.exp ((7 / 100 : ℝ) * D.n) := by
      calc
        D.starLik q W a.1 x y / D.starMarg q W a.1 y ≤
            (Real.exp ((3 / 100 : ℝ) * D.n) * D.starRef q W a.1 y) /
              D.starMarg q W a.1 y := div_le_div_of_nonneg_right hSL hMargPos.le
        _ = Real.exp ((3 / 100 : ℝ) * D.n) *
              (D.starRef q W a.1 y / D.starMarg q W a.1 y) := by ring
        _ ≤ Real.exp ((3 / 100 : ℝ) * D.n) * Real.exp ((4 / 100 : ℝ) * D.n) :=
              mul_le_mul_of_nonneg_left hRefLe (Real.exp_nonneg _)
        _ = Real.exp ((7 / 100 : ℝ) * D.n) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hrowEq : (D.N : ℝ) * D.evenRowAt q W a y x =
        ((D.N : ℝ) * (D.Usel q c).w x) *
          (D.starLik q W a.1 x y / D.starMarg q W a.1 y) := by
      unfold Ctx.evenRowAt
      field_simp [hMargNe]
      ring
    rw [hrowEq]
    calc
      ((D.N : ℝ) * (D.Usel q c).w x) *
          (D.starLik q W a.1 x y / D.starMarg q W a.1 y) ≤
        Real.exp ((3 / 100 : ℝ) * D.n) * Real.exp ((7 / 100 : ℝ) * D.n) :=
          mul_le_mul hUcap hFoverM (div_nonneg hLikNonneg hMargPos.le) (Real.exp_nonneg _)
      _ = Real.exp ((1 / 10 : ℝ) * D.n) := by rw [← Real.exp_add]; congr 1 <;> ring
  exact hRow

/-- L8.1l(iv) (08:441–449): integrating the role's anchor and the product neighbour data gives the data subdensity
`M_v`, which cancels the posterior denominator: `Σ_y M_v(y) w_v(x; y) 1[success] ≤ U_v(x) Σ_y F_x(y) ≤ U_v(x)`. -/
theorem star_cancel (D : Ctx η₀ β p h) (hU : D.StarRefUpdate) (hP : D.PRowFacts) : D.StarCancel := by
  classical
  intro q W a x
  let c := cellOf η₀ a.1
  let U := D.Usel q c
  have hLikInv : ∀ z t y,
      D.starLik q (Function.update W c z) a.1 t y = D.starLik q W a.1 t y := by
    intro z t y
    simp [Ctx.starLik, c, Function.update_idem]
  have hMargInv : ∀ z y,
      D.starMarg q (Function.update W c z) a.1 y = D.starMarg q W a.1 y := by
    intro z y
    unfold Ctx.starMarg
    apply Finset.sum_congr rfl
    intro t ht
    rw [hLikInv z t y]
  have hRowInv : ∀ z y,
      D.evenRowAt q (Function.update W c z) a y x = D.evenRowAt q W a y x := by
    intro z y
    unfold Ctx.evenRowAt
    rw [hLikInv z x y, hMargInv z y]
  have hPredInv : ∀ z y,
      D.PredFail q (Function.update W c z) a.1 y = D.PredFail q W a.1 y := by
    intro z y
    have href := congrFun (hU q W a.1 z) y
    unfold Ctx.PredFail
    rw [hMargInv z y]
    have href' : D.starRef q (Function.update W c z) a.1 y = D.starRef q W a.1 y := by
      simpa [c] using href
    rw [href']
  have hOuter : ∀ z y,
      (∏ j, D.prow q (Function.update W c z) (cellOf η₀ (cubeFlip a.1 j)) (y j)) =
        D.starLik q W a.1 z y := by
    intro z y
    rfl
  have prow_sum_le_one : ∀ W' c', ∑ t : Fin D.N, D.prow q W' c' t ≤ 1 := by
    intro W' c'
    by_cases hv : D.Valid8 q W' c'
    · have hs := ((hP q W' c').2.2 hv).1
      rw [hs]
    · simp [Ctx.prow, hv]
  have hLik_sum_le : ∀ z, ∑ y : Fin D.n → Fin D.N, D.starLik q W a.1 z y ≤ 1 := by
    intro z
    unfold Ctx.starLik
    rw [← Fintype.prod_sum]
    refine Finset.prod_le_one₀ ?_ ?_
    · intro j hj
      exact Finset.sum_nonneg fun t _ =>
        (hP q (Function.update W c z) (cellOf η₀ (cubeFlip a.1 j))).1 t
    · intro j hj
      exact prow_sum_le_one (Function.update W c z) (cellOf η₀ (cubeFlip a.1 j))
  have hF_nonneg : ∀ y : Fin D.n → Fin D.N, 0 ≤ D.starLik q W a.1 x y := by
    intro y
    unfold Ctx.starLik
    exact Finset.prod_nonneg fun j _ =>
      (hP q (Function.update W c x) (cellOf η₀ (cubeFlip a.1 j))).1 (y j)
  have hInner : ∀ y : Fin D.n → Fin D.N,
      ∑ z, U.w z *
        (D.starLik q W a.1 z y *
          ((if D.PredFail q W a.1 y then 0 else 1) *
            (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y)))) =
        (if D.PredFail q W a.1 y then 0 else 1) *
          (D.N * D.starLik q W a.1 x y * U.w x) := by
    intro y
    by_cases hf : D.PredFail q W a.1 y
    · simp [hf]
    · have hmne : D.starMarg q W a.1 y ≠ 0 := by
        intro hz
        exact hf (Or.inl hz)
      have hsum : ∑ z, U.w z * D.starLik q W a.1 z y = D.starMarg q W a.1 y := by
        rfl
      simp only [if_neg hf, one_mul]
      calc
        (∑ z, U.w z * (D.starLik q W a.1 z y *
            (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y)))) =
            (∑ z, U.w z * D.starLik q W a.1 z y) *
              (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y)) := by
                calc
                  _ = ∑ z, (U.w z * D.starLik q W a.1 z y) *
                        (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y)) := by
                          apply Finset.sum_congr rfl
                          intro z hz
                          ring
                  _ = _ := (Finset.sum_mul Finset.univ
                    (fun z => U.w z * D.starLik q W a.1 z y)
                    (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y))).symm
        _ = D.starMarg q W a.1 y *
              (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y)) := by rw [hsum]
        _ = D.N * D.starLik q W a.1 x y * U.w x := by field_simp [hmne]
  calc
    ∑ z, U.w z * D.evenStar q (Function.update W c z) a x =
        ∑ y : Fin D.n → Fin D.N, ∑ z,
          U.w z * (D.starLik q W a.1 z y *
            ((if D.PredFail q W a.1 y then 0 else 1) *
              (D.N * (D.starLik q W a.1 x y * U.w x / D.starMarg q W a.1 y)))) := by
          unfold Ctx.evenStar
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y hy
          apply Finset.sum_congr rfl
          intro z hz
          rw [hOuter z y, hPredInv z y, hRowInv z y]
          simp [Ctx.evenRowAt, U, c]
    _ = ∑ y : Fin D.n → Fin D.N,
          (if D.PredFail q W a.1 y then 0 else 1) *
            (D.N * D.starLik q W a.1 x y * U.w x) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact hInner y
    _ ≤ D.N * U.w x := by
          have hscale : 0 ≤ D.N * U.w x := mul_nonneg (Nat.cast_nonneg _) (U.nonneg x)
          calc
            (∑ y : Fin D.n → Fin D.N,
                (if D.PredFail q W a.1 y then 0 else 1) *
                  (D.N * D.starLik q W a.1 x y * U.w x)) ≤
                ∑ y : Fin D.n → Fin D.N, D.N * D.starLik q W a.1 x y * U.w x := by
                  apply Finset.sum_le_sum
                  intro y hy
                  by_cases hf : D.PredFail q W a.1 y
                  · simp [hf, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hF_nonneg y)) (U.nonneg x)]
                  · simp [hf]
            _ = (D.N * U.w x) * ∑ y : Fin D.n → Fin D.N, D.starLik q W a.1 x y := by
                  calc
                    _ = ∑ y : Fin D.n → Fin D.N, (D.N * U.w x) * D.starLik q W a.1 x y := by
                          apply Finset.sum_congr rfl
                          intro y hy
                          ring
                    _ = _ := (Finset.mul_sum Finset.univ
                      (fun y => D.starLik q W a.1 x y) (D.N * U.w x)).symm
            _ ≤ D.N * U.w x := by
                  simpa using mul_le_mul_of_nonneg_left (hLik_sum_le x) hscale

/-- L8.1l(v) (08:439): residual-separated even roles have disjoint odd neighbourhoods; the clock law is supported
on predictive success and its joint comparison on the at most `n^2` neighbouring odd labels replaces the injection
by independent draws from the odd rows; the integral factors into the star integrals. -/
theorem clock_factor (D : Ctx η₀ β p h) (q : D.Pre) (J : D.Anch → FinProb (OddRole D.n → Fin D.N))
    (hJ : ∀ W, D.GoodPre q W → D.ClockOK q W (J W)) (hP : D.PRowFacts) : D.ClockFactor q J := by
  classical
  intro W hg x l hl a hsep
  by_cases hl0 : l = 0
  · subst l
    simp [Finset.prod_empty, (J W).sum_eq_one]
  · have hnpos : 0 < D.n := by omega
    have hresEdge (v : CubeVertex D.n) (j : Fin D.n) :
        _root_.hammingDist (resOf η₀ v) (resOf η₀ (cubeFlip v j)) ≤ 1 := by
      classical
      change (Finset.univ.filter (fun t : Fin (dC η₀ D.n) =>
        resOf η₀ v t ≠ resOf η₀ (cubeFlip v j) t)).card ≤ 1
      let rIndex (t : Fin (dC η₀ D.n)) : Fin D.n :=
        ⟨mC η₀ D.n + t.val, by have ht := t.isLt; unfold dC at ht; omega⟩
      have hrIndex_inj : Function.Injective rIndex := by
        intro s t hst
        have hval := congrArg Fin.val hst
        change mC η₀ D.n + s.val = mC η₀ D.n + t.val at hval
        exact Fin.ext (Nat.add_left_cancel hval)
      have hdiff : ∀ t, resOf η₀ v t ≠ resOf η₀ (cubeFlip v j) t → rIndex t = j := by
        intro t ht
        by_contra hne
        apply ht
        change v (rIndex t) = Function.update v j (!v j) (rIndex t)
        exact (Function.update_of_ne hne _ _).symm
      by_cases hex : ∃ t, rIndex t = j
      · obtain ⟨t₀, ht₀⟩ := hex
        have hsubset : Finset.univ.filter
            (fun t : Fin (dC η₀ D.n) => resOf η₀ v t ≠ resOf η₀ (cubeFlip v j) t) ⊆ {t₀} := by
          intro t ht
          apply Finset.mem_singleton.mpr
          apply hrIndex_inj
          exact (hdiff t (Finset.mem_filter.mp ht).2).trans ht₀.symm
        calc
          _ ≤ ({t₀} : Finset (Fin (dC η₀ D.n))).card := Finset.card_le_card hsubset
          _ = 1 := Finset.card_singleton t₀
      · have hempty : Finset.univ.filter
            (fun t : Fin (dC η₀ D.n) => resOf η₀ v t ≠ resOf η₀ (cubeFlip v j) t) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hex ⟨t, hdiff t (Finset.mem_filter.mp ht).2⟩
        simp [hempty]
    have hflip_inj (v : CubeVertex D.n) : Function.Injective (cubeFlip v) := by
      intro j k hjk
      by_contra hjk'
      have hAt := congrFun hjk j
      cases hv : v j <;> simp [cubeFlip, hjk', hv] at hAt
    let roleMap : Fin l × Fin D.n → OddRole D.n := fun ij => oddNbr (a ij.1) ij.2
    have hroleMap_inj : Function.Injective roleMap := by
      intro ij kl heq
      have hverts : cubeFlip (a ij.1).1 ij.2 = cubeFlip (a kl.1).1 kl.2 := congrArg Subtype.val heq
      have hresEq : resOf η₀ (roleMap ij).1 = resOf η₀ (roleMap kl).1 := congrArg (resOf η₀) hverts
      have hdist : _root_.hammingDist (resOf η₀ (a ij.1).1) (resOf η₀ (a kl.1).1) ≤ 2 := by
        calc
          _ ≤ _root_.hammingDist (resOf η₀ (a ij.1).1) (resOf η₀ (roleMap ij).1) +
              _root_.hammingDist (resOf η₀ (roleMap ij).1) (resOf η₀ (a kl.1).1) :=
                hammingDist_triangle _ _ _
          _ = _root_.hammingDist (resOf η₀ (a ij.1).1) (resOf η₀ (roleMap ij).1) +
              _root_.hammingDist (resOf η₀ (roleMap kl).1) (resOf η₀ (a kl.1).1) := by rw [hresEq]
          _ ≤ 1 + 1 := add_le_add
                (by simpa [roleMap, oddNbr] using hresEdge (a ij.1).1 ij.2)
                (by simpa [roleMap, oddNbr, hammingDist_comm] using hresEdge (a kl.1).1 kl.2)
          _ = 2 := by norm_num
      by_cases hik : ij.1 = kl.1
      · have hsecond : ij.2 = kl.2 := by
          apply hflip_inj (a ij.1).1
          simpa [hik] using hverts
        exact Prod.ext hik hsecond
      · have hfar := hsep ij.1 kl.1 hik
        omega
    let S : Finset (OddRole D.n) := Finset.univ.image roleMap
    have hScardNat : S.card = l * D.n := by
      dsimp [S]
      rw [Finset.card_image_of_injective Finset.univ hroleMap_inj]
      simp
    have hScard : (S.card : ℝ) ≤ (D.n : ℝ) ^ 3 := by
      have hlcast : (l : ℝ) ≤ D.n := by exact_mod_cast hl
      have hncast : (1 : ℝ) ≤ D.n := by exact_mod_cast (Nat.succ_le_of_lt hnpos)
      rw [hScardNat, Nat.cast_mul]
      calc
        (l : ℝ) * D.n ≤ (D.n : ℝ) * D.n := mul_le_mul_of_nonneg_right hlcast (by positivity)
        _ ≤ (D.n : ℝ) ^ 3 := by
          calc
            (D.n : ℝ) * D.n = (D.n : ℝ) ^ 2 := by ring
            _ = 1 * (D.n : ℝ) ^ 2 := by ring
            _ ≤ (D.n : ℝ) * (D.n : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hncast (sq_nonneg (D.n : ℝ))
            _ = (D.n : ℝ) ^ 3 := by ring
    have hmem (ij : Fin l × Fin D.n) : roleMap ij ∈ S :=
      Finset.mem_image.mpr ⟨ij, Finset.mem_univ _, rfl⟩
    let nbrMap : Fin l × Fin D.n → S := fun ij => ⟨roleMap ij, hmem ij⟩
    have hnbrMap_inj : Function.Injective nbrMap := by
      intro ij kl heq
      apply hroleMap_inj
      exact congrArg Subtype.val heq
    have hnbrMap_surj : Function.Surjective nbrMap := by
      intro u
      rcases Finset.mem_image.mp u.2 with ⟨ij, _, hEq⟩
      refine ⟨ij, ?_⟩
      apply Subtype.ext
      exact hEq
    let nbrEquiv : Fin l × Fin D.n ≃ S := Equiv.ofBijective nbrMap ⟨hnbrMap_inj, hnbrMap_surj⟩
    let labels : (S → Fin D.N) → Fin l → Fin D.n → Fin D.N :=
      fun g i j => g (nbrMap (i, j))
    let assignEquiv : (S → Fin D.N) ≃ (Fin l → Fin D.n → Fin D.N) :=
      { toFun := fun (g : S → Fin D.N) (i : Fin l) (j : Fin D.n) => g (nbrEquiv (i, j))
        invFun := fun (y : Fin l → Fin D.n → Fin D.N) (u : S) =>
          y (nbrEquiv.symm u).1 (nbrEquiv.symm u).2
        left_inv := by
          intro g
          funext u
          simp
        right_inv := by
          intro y
          funext i
          funext j
          simp }
    have hRowNN : ∀ aa y, 0 ≤ D.evenRowAt q W aa y x := by
      intro aa y
      have hlik : 0 ≤ D.starLik q W aa.1 x y := by
        unfold Ctx.starLik
        exact Finset.prod_nonneg fun j _ =>
          (hP q (Function.update W (cellOf η₀ aa.1) x) (cellOf η₀ (cubeFlip aa.1 j))).1 (y j)
      have hmarg : 0 ≤ D.starMarg q W aa.1 y := by
        unfold Ctx.starMarg
        exact Finset.sum_nonneg fun z _ => mul_nonneg
          ((D.Usel q (cellOf η₀ aa.1)).nonneg z)
          (by
            unfold Ctx.starLik
            exact Finset.prod_nonneg fun j _ =>
              (hP q (Function.update W (cellOf η₀ aa.1) z)
                (cellOf η₀ (cubeFlip aa.1 j))).1 (y j))
      exact div_nonneg (mul_nonneg hlik ((D.Usel q (cellOf η₀ aa.1)).nonneg x)) hmarg
    let rawWeight (g : S → Fin D.N) : ℝ :=
      ∏ u : S, D.prow q W (cellOf η₀ u.1) (g u)
    let success (g : S → Fin D.N) : Prop :=
      ∀ i : Fin l, ¬ D.PredFail q W (a i).1 (labels g i)
    let phi (g : S → Fin D.N) : ℝ :=
      (if success g then 1 else 0) *
        ∏ i : Fin l, (D.N : ℝ) * D.evenRowAt q W (a i) (labels g i) x
    have hphi_nonneg : ∀ g, 0 ≤ phi g := by
      intro g
      unfold phi
      have hI : (0 : ℝ) ≤ (if success g then 1 else 0 : ℝ) := by split_ifs <;> norm_num
      exact mul_nonneg hI (Finset.prod_nonneg fun i _ =>
        mul_nonneg (Nat.cast_nonneg _) (hRowNN (a i) (labels g i)))
    have hlabels_restrict (f : OddRole D.n → Fin D.N) (i : Fin l) :
        labels (fun u : S => f u.1) i = nbrLabels f (a i) := by
      funext j
      simp [labels, nbrMap, roleMap, nbrLabels, oddNbr]
    let hClock := hJ W hg
    have hOriginal :
        ∑ f, (J W).w f * ∏ i : Fin l, (D.N : ℝ) * D.evenRow q W f (a i) x =
          (J W).expect (fun f => phi (fun u : S => f u.1)) := by
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hw : (J W).w f = 0
      · simp [hw]
      · have hsupp := hClock.1 f hw
        have hsuccess : success (fun u : S => f u.1) := by
          intro i
          simpa [hlabels_restrict f i] using hsupp.2 (a i)
        simp [phi, hsuccess, hlabels_restrict, Ctx.evenRow]
    have hnonempty : Nonempty (OddRole D.n → Fin D.N) := by
      by_contra hne
      haveI : IsEmpty (OddRole D.n → Fin D.N) := ⟨fun f => hne ⟨f⟩⟩
      have hs : (∑ f : OddRole D.n → Fin D.N, (J W).w f) = 0 := by simp
      rw [(J W).sum_eq_one] at hs
      norm_num at hs
    let f₀ : OddRole D.n → Fin D.N := Classical.choice hnonempty
    let restrict (f : OddRole D.n → Fin D.N) : S → Fin D.N := fun u => f u.1
    let mapped : FinProb (S → Fin D.N) := FinProb.map (J W) restrict
    have hmap_weight : ∀ g : S → Fin D.N,
        mapped.w g ≤ 2 * rawWeight g := by
      intro g
      let o : OddRole D.n → Fin D.N := fun u => if hu : u ∈ S then g ⟨u, hu⟩ else f₀ u
      have hcondition (f : OddRole D.n → Fin D.N) :
          restrict f = g ↔ ∀ u ∈ S, f u = o u := by
        constructor
        · intro he u hu
          have h := congrFun he ⟨u, hu⟩
          simpa [o, hu] using h
        · intro he
          funext u
          simpa [o, u.2] using he u.1 u.2
      have hmass : mapped.w g = (J W).pr (fun f => ∀ u ∈ S, f u = o u) := by
        unfold mapped
        unfold FinProb.map FinProb.pr
        apply Finset.sum_congr rfl
        intro f hf
        by_cases he : restrict f = g
        · have hevent : ∀ u ∈ S, f u = o u := hcondition f |>.mp he
          simp only [if_pos he, if_pos hevent]
        · have hnevent : ¬ ∀ u ∈ S, f u = o u := fun h => he (hcondition f |>.mpr h)
          simp only [if_neg he, if_neg hnevent]
      have hbound := hClock.2 S o hScard
      have hprod : rawWeight g = ∏ u ∈ S, D.prow q W (cellOf η₀ u) (o u) := by
        unfold rawWeight
        let rowFun : OddRole D.n → ℝ := fun u => D.prow q W (cellOf η₀ u) (o u)
        calc
          (∏ u : S, D.prow q W (cellOf η₀ u.1) (g u)) =
              ∏ u : S, rowFun u.1 := by
                apply Finset.prod_congr rfl
                intro u hu
                simp [rowFun, o, u.2]
          _ = ∏ u ∈ S, rowFun u := by
                rw [Finset.univ_eq_attach]
                exact Finset.prod_attach S rowFun
      calc
        mapped.w g = (J W).pr (fun f => ∀ u ∈ S, f u = o u) := hmass
        _ ≤ 2 * ∏ u ∈ S, D.prow q W (cellOf η₀ u) (o u) := hbound
        _ = 2 * rawWeight g := by rw [hprod]
    have hdom : (J W).expect (fun f => phi (restrict f)) ≤
        2 * ∑ g : S → Fin D.N, rawWeight g * phi g := by
      calc
        (J W).expect (fun f => phi (restrict f)) = mapped.expect phi := by
          simpa [mapped, restrict] using (FinProb.map_expect (J W) restrict phi).symm
        _ = ∑ g, mapped.w g * phi g := rfl
        _ ≤ ∑ g, (2 * rawWeight g) * phi g :=
          Finset.sum_le_sum fun g hg => mul_le_mul_of_nonneg_right (hmap_weight g) (hphi_nonneg g)
        _ = 2 * ∑ g, rawWeight g * phi g := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g hg
          ring
    let localFactor (i : Fin l) (y : Fin D.n → Fin D.N) : ℝ :=
      (∏ j, D.prow q W (cellOf η₀ (cubeFlip (a i).1 j)) (y j)) *
        ((if D.PredFail q W (a i).1 y then 0 else 1) *
          ((D.N : ℝ) * D.evenRowAt q W (a i) y x))
    have hindicator (g : S → Fin D.N) :
        (if success g then (1 : ℝ) else 0) = ∏ i : Fin l,
          (if D.PredFail q W (a i).1 (labels g i) then (0 : ℝ) else 1) := by
      by_cases hs : success g
      · simp [hs, success]
      · have hs' : ¬ ∀ i : Fin l, ¬ D.PredFail q W (a i).1 (labels g i) := by
          simpa [success] using hs
        push_neg at hs'
        obtain ⟨i, hi⟩ := hs'
        have hfail : D.PredFail q W (a i).1 (labels g i) := hi
        have hfactor : (if D.PredFail q W (a i).1 (labels g i) then (0 : ℝ) else 1) = 0 := if_pos hfail
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hfactor]
        simp [hs]
    have hrawpoint (g : S → Fin D.N) :
        rawWeight g * phi g = ∏ i : Fin l, localFactor i (labels g i) := by
      have hprodWeight : rawWeight g = ∏ i : Fin l,
          ∏ j : Fin D.n, D.prow q W (cellOf η₀ (cubeFlip (a i).1 j)) (labels g i j) := by
        unfold rawWeight
        calc
          (∏ u : S, D.prow q W (cellOf η₀ u.1) (g u)) =
              ∏ ij : Fin l × Fin D.n,
                D.prow q W (cellOf η₀ (roleMap ij).1) (g (nbrMap ij)) :=
                (Fintype.prod_equiv nbrEquiv
                  (fun ij : Fin l × Fin D.n =>
                    D.prow q W (cellOf η₀ (roleMap ij).1) (g (nbrMap ij)))
                  (fun u : S => D.prow q W (cellOf η₀ u.1) (g u)) (by intro ij; rfl)).symm
          _ = ∏ i : Fin l, ∏ j : Fin D.n,
                D.prow q W (cellOf η₀ (cubeFlip (a i).1 j)) (labels g i j) := by
                rw [Fintype.prod_prod_type]
                apply Fintype.prod_congr
                intro i
                apply Fintype.prod_congr
                intro j
                simp [labels, nbrMap, roleMap, oddNbr]
      calc
        rawWeight g * phi g =
            rawWeight g * ((if success g then 1 else 0) *
              ∏ i : Fin l, (D.N : ℝ) * D.evenRowAt q W (a i) (labels g i) x) := rfl
        _ = rawWeight g *
              ((∏ i : Fin l, (if D.PredFail q W (a i).1 (labels g i) then 0 else 1)) *
                ∏ i : Fin l, (D.N : ℝ) * D.evenRowAt q W (a i) (labels g i) x) := by
                  exact congrArg
                    (fun t : ℝ => rawWeight g * (t * ∏ i : Fin l, (D.N : ℝ) *
                      D.evenRowAt q W (a i) (labels g i) x)) (hindicator g)
        _ = ∏ i : Fin l, localFactor i (labels g i) := by
              rw [hprodWeight]
              unfold localFactor
              have hprod_distrib :
                  (∏ i : Fin l,
                    (∏ j : Fin D.n,
                      D.prow q W (cellOf η₀ (cubeFlip (a i).1 j)) (labels g i j)) *
                      ((if D.PredFail q W (a i).1 (labels g i) then (0 : ℝ) else 1) *
                        ((D.N : ℝ) * D.evenRowAt q W (a i) (labels g i) x))) =
                    (∏ i : Fin l, ∏ j : Fin D.n,
                      D.prow q W (cellOf η₀ (cubeFlip (a i).1 j)) (labels g i j)) *
                      ((∏ i : Fin l,
                        (if D.PredFail q W (a i).1 (labels g i) then (0 : ℝ) else 1)) *
                        ∏ i : Fin l, (D.N : ℝ) * D.evenRowAt q W (a i) (labels g i) x) := by
                rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
              exact hprod_distrib.symm
    have hrawsum :
        ∑ g : S → Fin D.N, rawWeight g * phi g = ∏ i : Fin l, D.evenStar q W (a i) x := by
      calc
        ∑ g : S → Fin D.N, rawWeight g * phi g =
            ∑ y : Fin l → Fin D.n → Fin D.N, ∏ i : Fin l, localFactor i (y i) := by
              rw [← Equiv.sum_comp assignEquiv (fun y => ∏ i, localFactor i (y i))]
              apply Finset.sum_congr rfl
              intro g hg
              rw [hrawpoint g]
              apply Finset.prod_congr rfl
              intro i hi
              apply congrArg (localFactor i)
              funext j
              change g (nbrMap (i, j)) = g (nbrMap (i, j))
              rfl
        _ = ∏ i : Fin l, ∑ y : Fin D.n → Fin D.N, localFactor i y := by
              rw [← Fintype.prod_sum]
        _ = ∏ i : Fin l, D.evenStar q W (a i) x := by
              apply Finset.prod_congr rfl
              intro i hi
              rfl
    calc
      ∑ f, (J W).w f * ∏ i : Fin l, (D.N : ℝ) * D.evenRow q W f (a i) x =
          (J W).expect (fun f => phi (fun u : S => f u.1)) := hOriginal
      _ ≤ 2 * ∑ g : S → Fin D.N, rawWeight g * phi g := hdom
      _ = 2 * ∏ i : Fin l, D.evenStar q W (a i) x := by rw [hrawsum]

set_option maxHeartbeats 1000000 in
/-- L8.1l(vi) (08:439–449): remove the anchor events touching the separated target anchors (at most
`(2s + n - m + 1)^2` each, factor `2` per role, `CondProductBound`); each star integral reads anchors within cell
distance two of its own target only (targets more than four apart), so the targets integrate independently and
`StarCancel` bounds each factor. -/
theorem even_anchor_integral (cA : ℝ) (hcA : 0 < cA) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → CondProductBound → D.StarCancel →
      D.PRowFacts → ∀ q : D.Pre, D.Good q → D.AnchorLLL q (2 * Real.exp (-(D.n : ℝ) ^ cA)) →
        D.EvenAnchorIntegral q := by
  classical
  have hAtTop : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ cA)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hcA).comp tendsto_natCast_atTop_atTop
  have hdecayT : Filter.Tendsto
      (fun t : ℝ => t ^ (5 / cA) * Real.exp (-t)) Filter.atTop (nhds 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / cA) 1 (by norm_num)
  have hdecay := hdecayT.comp hAtTop
  have hsmallRaw : ∀ᶠ n : ℕ in Filter.atTop,
      ((n : ℝ) ^ cA) ^ (5 / cA) * Real.exp (-((n : ℝ) ^ cA)) < 1 / 2056 :=
    hdecay.eventually (Iio_mem_nhds (by norm_num))
  have hpowerEq (n : ℕ) (hn : 1 ≤ n) :
      (n : ℝ) ^ 5 = ((n : ℝ) ^ cA) ^ (5 / cA) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    calc
      (n : ℝ) ^ 5 = (n : ℝ) ^ (5 : ℝ) := (Real.rpow_natCast (n : ℝ) 5).symm
      _ = (n : ℝ) ^ (cA * (5 / cA)) := by
        congr 1
        field_simp [ne_of_gt hcA] <;> ring
      _ = ((n : ℝ) ^ cA) ^ (5 / cA) := Real.rpow_mul hnpos.le _ _
  have hsmallNat : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 5 * Real.exp (-((n : ℝ) ^ cA)) < 1 / 2056 := by
    filter_upwards [hsmallRaw, Filter.eventually_ge_atTop 1] with n hsmall hn
    rw [hpowerEq n hn]
    simpa using hsmall
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hsmallNat
  refine ⟨n₀, ?_⟩
  intro D hn hG hCP hCan hP q hq hALL x l hl a hsep
  by_cases hl0 : l = 0
  · subst l
    haveI : IsEmpty (Fin 0) := inferInstance
    have hprodW (W : D.Anch) :
        (∏ i : Fin 0, D.evenStar q W (a i) x) = 1 := by
      change (∏ i ∈ (Finset.univ : Finset (Fin 0)), D.evenStar q W (a i) x) = 1
      rw [Finset.univ_eq_empty]
      simp
    have hprodU :
        (∏ i : Fin 0, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x) = 1 := by
      change (∏ i ∈ (Finset.univ : Finset (Fin 0)),
        (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x) = 1
      rw [Finset.univ_eq_empty]
      simp
    simp_rw [hprodW, hprodU]
    change (D.anchorLaw q).expect (fun _ => (1 : ℝ)) ≤ (2 : ℝ) ^ 0 * 1
    rw [FinProb.expect_const]
    norm_num
  have hlpos : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr (by simpa using hl0)
  have hsmallD := hn₀ D.n hn
  have hsleM : sC η₀ D.n ≤ mC η₀ D.n := by
    rw [mC]
    calc
      sC η₀ D.n = sC η₀ D.n * 1 := by simp
      _ ≤ sC η₀ D.n * lC D.n := Nat.mul_le_mul_left _ hG.pos.2.1
  have hmle : mC η₀ D.n ≤ D.n := by
    calc
      mC η₀ D.n ≤ 2 * mC η₀ D.n := by omega
      _ ≤ D.n := hG.split
  have hsle : sC η₀ D.n ≤ D.n := hsleM.trans hmle
  have hdle : dC η₀ D.n ≤ D.n := Nat.sub_le _ _
  have hbaseNat : 2 * sC η₀ D.n + dC η₀ D.n + 1 ≤ 4 * D.n := by omega
  let dgr : ℕ := (2 * sC η₀ D.n + dC η₀ D.n + 1) ^ 4
  have hnR : 1 ≤ (D.n : ℝ) := by exact_mod_cast hG.pos.1
  have hbaseR : (2 * sC η₀ D.n + dC η₀ D.n + 1 : ℕ) ≤ 4 * (D.n : ℝ) := by
    exact_mod_cast hbaseNat
  have hn4 : (1 : ℝ) ≤ (D.n : ℝ) ^ 4 := by
    calc
      (1 : ℝ) = 1 ^ (4 : ℕ) := by norm_num
      _ ≤ (D.n : ℝ) ^ 4 := by gcongr
  have hdegree : (dgr : ℝ) + 1 ≤ 257 * (D.n : ℝ) ^ 4 := by
    dsimp [dgr]
    push_cast
    have hbaseR' : 2 * (sC η₀ D.n : ℝ) + dC η₀ D.n + 1 ≤ 4 * (D.n : ℝ) := by
      exact_mod_cast hbaseNat
    calc
      (2 * (sC η₀ D.n : ℝ) + dC η₀ D.n + 1) ^ 4 + 1 ≤
          (4 * (D.n : ℝ)) ^ 4 + 1 := by
            have hpowR := pow_le_pow_left₀ (by positivity) hbaseR' 4
            exact add_le_add hpowR le_rfl
      _ = 256 * (D.n : ℝ) ^ 4 + 1 := by ring
      _ ≤ 257 * (D.n : ℝ) ^ 4 := by nlinarith [hn4]
  let xLLL : ℝ := 2 * Real.exp (-((D.n : ℝ) ^ cA))
  have hproductSmall : (dgr + 1 : ℕ) * xLLL * (D.n : ℝ) ≤ 1 / 4 := by
    have hxNN : 0 ≤ xLLL := by positivity
    calc
      ((dgr + 1 : ℕ) : ℝ) * xLLL * (D.n : ℝ) ≤
          (257 * (D.n : ℝ) ^ 4) * xLLL * (D.n : ℝ) := by
            calc
              _ = (((dgr : ℝ) + 1) * xLLL) * (D.n : ℝ) := by simp [mul_assoc]
              _ ≤ (257 * (D.n : ℝ) ^ 4 * xLLL) * (D.n : ℝ) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hdegree hxNN) (by linarith [hnR])
      _ = 514 * (D.n : ℝ) ^ 5 * Real.exp (-((D.n : ℝ) ^ cA)) := by ring
      _ ≤ 514 * (1 / 2056) := by
            calc
              _ = 514 * ((D.n : ℝ) ^ 5 * Real.exp (-((D.n : ℝ) ^ cA))) := by ring
              _ ≤ 514 * (1 / 2056) := mul_le_mul_of_nonneg_left hsmallD.le (by norm_num)
      _ = 1 / 4 := by norm_num
  let target (i : Fin l) : D.CellT := cellOf η₀ (a i).1
  let scope (i : Fin l) : Finset D.CellT := cellBall (target i) 2
  let U : Finset D.CellT := Finset.univ.biUnion scope
  let Φ : D.Anch → ℝ := fun W => ∏ i : Fin l, D.evenStar q W (a i) x
  have hStarNN (W : D.Anch) (aa : EvenRole D.n) : 0 ≤ D.evenStar q W aa x :=
    evenStar_nonneg D hP q W aa x
  have hPhiNN : ∀ W, 0 ≤ Φ W := by
    intro W
    apply Finset.prod_nonneg
    intro i hi
    exact hStarNN W (a i)
  have hPhiDep : FinProb.DependsOn Φ U := by
    intro W W' hAgree
    apply Finset.prod_congr rfl
    intro i hi
    have hlocal := evenStar_depends_ball_two D hG q (a i) x
    apply hlocal W W'
    intro c hc
    exact hAgree c (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩)
  have hballDisjoint (i j : Fin l) (hij : i ≠ j) : Disjoint (scope i) (scope j) := by
    apply Finset.disjoint_left.mpr
    intro c hci hcj
    have hci' := (Finset.mem_filter.mp hci).2
    have hcj' := (Finset.mem_filter.mp hcj).2
    have hctj : cellDist c (target j) ≤ 2 := by
      simpa [cellDist_symm] using hcj'
    have hdist : cellDist (target i) (target j) ≤ 4 := by
      calc
        cellDist (target i) (target j) ≤ cellDist (target i) c + cellDist c (target j) :=
          cellDist_triangle _ _ _
        _ ≤ 2 + 2 := Nat.add_le_add hci' hctj
    have hres : _root_.hammingDist (resOf η₀ (a i).1) (resOf η₀ (a j).1) ≤ 4 := by
      have hresle : _root_.hammingDist (resOf η₀ (a i).1) (resOf η₀ (a j).1) ≤
          cellDist (target i) (target j) := by
        unfold cellDist
        exact Nat.le_add_left _ _
      exact hresle.trans hdist
    have hfar := hsep i j hij
    omega
  have hFactorEq :
      (D.rawAnchors q).expect Φ =
        ∏ i : Fin l, (D.rawAnchors q).expect (fun W => D.evenStar q W (a i) x) := by
    simpa [Φ, scope, Ctx.rawAnchors] using
      (pi_expect_prod_of_disjoint (fun c : D.CellT => D.Usel q c)
        (fun i W => D.evenStar q W (a i) x) scope Finset.univ
        (by
          intro i hi
          exact evenStar_depends_ball_two D hG q (a i) x)
        (by
          intro i hi j hj hij
          exact hballDisjoint i j hij))
  have hSingle (i : Fin l) :
      (D.rawAnchors q).expect (fun W => D.evenStar q W (a i) x) ≤
        (D.N : ℝ) * (D.Usel q (target i)).w x := by
    simpa [target] using raw_evenStar_le D q (a i) x hCan
  have hRawBound : (D.rawAnchors q).expect Φ ≤
      ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x := by
    rw [hFactorEq]
    apply Finset.prod_le_prod₀
    · intro i hi
      unfold FinProb.expect
      apply Finset.sum_nonneg
      intro W hW
      exact mul_nonneg ((D.rawAnchors q).nonneg W) (hStarNN W (a i))
    · intro i hi
      exact hSingle i
  have htargetNN : 0 ≤ ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x := by
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (Nat.cast_nonneg _) ((D.Usel q (target i)).nonneg x)
  have hFiber : ∀ ω : D.Anch,
      (∑ b : (∀ i : {i // i ∈ U}, Fin D.N),
          (∏ i : {i // i ∈ U}, (D.Usel q i.1).w (b i)) * Φ (glue U ω b)) ≤
        ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x := by
    intro ω
    have hMarg := FinProb.pi_marginal_expect (fun c : D.CellT => D.Usel q c) U
      (fun b => Φ (glue U ω b))
    have hpoint (W : D.Anch) : Φ (glue U ω (fun i => W i.1)) = Φ W := by
      apply hPhiDep
      intro c hc
      simp [glue, hc]
    have hFiberEq :
        (∑ b : (∀ i : {i // i ∈ U}, Fin D.N),
            (∏ i : {i // i ∈ U}, (D.Usel q i.1).w (b i)) * Φ (glue U ω b)) =
          (D.rawAnchors q).expect Φ := by
      calc
        _ = (FinProb.pi (fun i : {i // i ∈ U} => D.Usel q i.1)).expect
              (fun b => Φ (glue U ω b)) := rfl
        _ = (D.rawAnchors q).expect (fun W => Φ (glue U ω (fun i => W i.1)) ) := hMarg.symm
        _ = (D.rawAnchors q).expect Φ := by
              unfold FinProb.expect
              apply Finset.sum_congr rfl
              intro W hW
              simpa using congrArg (fun t : ℝ => (D.rawAnchors q).w W * t) (hpoint W)
    rw [hFiberEq]
    exact hRawBound
  let badCell : D.CellT → D.Anch → Prop := fun c W => D.CellBad q W c
  have hLLL : LLLInput (fun c : D.CellT => D.Usel q c) badCell
      (fun c => cellBall c 2) xLLL dgr := by
    simpa [Ctx.AnchorLLL, badCell, xLLL, dgr] using hALL
  have hCond := hCP (fun c : D.CellT => D.Usel q c) badCell
    (fun c => cellBall c 2) xLLL dgr hLLL
  have hCondBound : (D.anchorLaw q).expect Φ ≤
      (2 : ℝ) ^ l * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x := by
    let touched : Finset D.CellT := Finset.univ.filter fun c =>
      ¬ Disjoint (cellBall c 2) U
    let touchOf (i : Fin l) : Finset D.CellT := Finset.univ.filter fun c =>
      ¬ Disjoint (cellBall c 2) (cellBall (target i) 2)
    let depOf (i : Fin l) : Finset D.CellT := Finset.univ.filter fun c =>
      c ≠ target i ∧ ¬ Disjoint (cellBall (target i) 2) (cellBall c 2)
    have hdepCard (i : Fin l) : (depOf i).card ≤ dgr := by
      simpa [depOf, dgr] using hLLL.degree (target i)
    have hTouchOfCard (i : Fin l) : (touchOf i).card ≤ dgr + 1 := by
      have hsub : touchOf i ⊆ insert (target i) (depOf i) := by
        intro c hc
        have hnot := (Finset.mem_filter.mp hc).2
        by_cases hct : c = target i
        · simp [hct]
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, hct, ?_⟩
          intro hdis
          apply hnot
          apply Finset.disjoint_left.mpr
          intro d hdc hdt
          exact (Finset.disjoint_left.mp hdis) hdt hdc
      calc
        (touchOf i).card ≤ (insert (target i) (depOf i)).card := Finset.card_le_card hsub
        _ ≤ (depOf i).card + 1 := Finset.card_insert_le _ _
        _ ≤ dgr + 1 := Nat.add_le_add_right (hdepCard i) 1
    have htouchSubset : touched ⊆ Finset.univ.biUnion touchOf := by
      intro c hc
      have hnot := (Finset.mem_filter.mp hc).2
      rcases Finset.not_disjoint_iff.mp hnot with ⟨d, hdc, hdu⟩
      rcases Finset.mem_biUnion.mp hdu with ⟨i, hi, hdi⟩
      have hmem : c ∈ touchOf i := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, Finset.not_disjoint_iff.mpr ⟨d, hdc, hdi⟩⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hmem⟩
    have hcount : touched.card ≤ l * (dgr + 1) := by
      calc
        touched.card ≤ (Finset.univ.biUnion touchOf).card := Finset.card_le_card htouchSubset
        _ ≤ ∑ i ∈ Finset.univ, (touchOf i).card := Finset.card_biUnion_le
        _ ≤ ∑ i ∈ Finset.univ, (dgr + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hTouchOfCard i
        _ = l * (dgr + 1) := by simp
    have htouchReal : (touched.card : ℝ) * xLLL ≤ 1 / 4 := by
      have hcountR : (touched.card : ℝ) ≤ (l : ℝ) * (dgr + 1 : ℝ) := by exact_mod_cast hcount
      have hlR : (l : ℝ) ≤ (D.n : ℝ) := by exact_mod_cast hl
      have hxNN : 0 ≤ xLLL := by positivity
      have hlin : (l : ℝ) * (dgr + 1 : ℝ) ≤
          (D.n : ℝ) * (dgr + 1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hlR (by positivity)
      calc
        (touched.card : ℝ) * xLLL ≤ ((l : ℝ) * (dgr + 1 : ℝ)) * xLLL :=
          mul_le_mul_of_nonneg_right hcountR hxNN
        _ ≤ ((D.n : ℝ) * (dgr + 1 : ℝ)) * xLLL :=
          mul_le_mul_of_nonneg_right hlin hxNN
        _ ≤ 1 / 4 := by
          have hprod : ((D.n : ℝ) * (dgr + 1 : ℝ)) * xLLL ≤ 1 / 4 := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hproductSmall
          exact hprod
    have hxNonneg : 0 ≤ xLLL := by positivity
    have hxLe : xLLL ≤ 1 / 4 := by
      have hdegreePos : (1 : ℝ) ≤ (dgr + 1 : ℝ) := by
        exact_mod_cast (show 1 ≤ dgr + 1 by omega)
      have hscale : 1 ≤ (dgr + 1 : ℝ) * (D.n : ℝ) := by
        have hprodNN : 0 ≤ ((dgr + 1 : ℝ) - 1) * ((D.n : ℝ) - 1) :=
          mul_nonneg (sub_nonneg.mpr hdegreePos) (sub_nonneg.mpr hnR)
        nlinarith [hprodNN]
      calc
        xLLL = 1 * xLLL := by ring
        _ ≤ ((dgr + 1 : ℝ) * (D.n : ℝ)) * xLLL :=
          mul_le_mul_of_nonneg_right hscale hxNonneg
        _ ≤ 1 / 4 := by
          have hprod : ((D.n : ℝ) * (dgr + 1 : ℝ)) * xLLL ≤ 1 / 4 := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hproductSmall
          nlinarith [hprod]
    have hInv := HypercubeRamsey.Clock.inv_one_sub_pow_le
      (m := touched.card) hxNonneg hxLe htouchReal
    have hloss : ((1 - xLLL) ^ touched.card)⁻¹ ≤ (2 : ℝ) ^ l := by
      rw [← inv_pow]
      calc
        ((1 - xLLL)⁻¹) ^ touched.card ≤ 2 := by
          calc
            _ ≤ 1 + (4 / 3 : ℝ) * (touched.card : ℝ) * xLLL := hInv
            _ ≤ 4 / 3 := by nlinarith [htouchReal]
            _ ≤ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ l := by
          cases l with
          | zero => omega
          | succ l =>
              rw [pow_succ]
              have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ l := one_le_pow₀ (by norm_num)
              nlinarith
    have hcp := hCond.2 U Φ hPhiNN
      (∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x) hFiber
    have hcp' : (D.anchorLaw q).expect Φ ≤
        ((1 - xLLL) ^ touched.card)⁻¹ *
          ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x := by
      simpa [Ctx.anchorLaw, Ctx.rawAnchors, badCell, U, scope, Φ, xLLL, dgr, touched] using hcp
    exact hcp'.trans (mul_le_mul_of_nonneg_right hloss htargetNN)
  have hFactorBound : (D.anchorLaw q).expect Φ ≤
      (2 : ℝ) ^ l * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (target i)).w x :=
    hCondBound
  exact hFactorBound

/-- L8.1l(vii) (08:439–453): the clock comparison at every successful prehistory and the anchor integral give
`4^l ∏ N U(x)` (for `l = 0` both sides are at most one). -/
theorem even_moment (D : Ctx η₀ β p h) (q : D.Pre) (J : D.Anch → FinProb (OddRole D.n → Fin D.N))
    (hP : D.PRowFacts) (hfac : D.ClockFactor q J) (hint : D.EvenAnchorIntegral q) : D.EvenMoment q J := by
  classical
  intro x l hl a hsep
  have hRowNN : ∀ W aa y xx, 0 ≤ D.evenRowAt q W aa y xx := by
    intro W aa y xx
    have hlik : 0 ≤ D.starLik q W aa.1 xx y := by
      unfold Ctx.starLik
      exact Finset.prod_nonneg fun j _ =>
        (hP q (Function.update W (cellOf η₀ aa.1) xx) (cellOf η₀ (cubeFlip aa.1 j))).1 (y j)
    have hmarg : 0 ≤ D.starMarg q W aa.1 y := by
      unfold Ctx.starMarg
      exact Finset.sum_nonneg fun z _ => mul_nonneg
        ((D.Usel q (cellOf η₀ aa.1)).nonneg z)
        (by
          unfold Ctx.starLik
          exact Finset.prod_nonneg fun j _ =>
            (hP q (Function.update W (cellOf η₀ aa.1) z)
              (cellOf η₀ (cubeFlip aa.1 j))).1 (y j))
    exact div_nonneg (mul_nonneg hlik ((D.Usel q (cellOf η₀ aa.1)).nonneg xx)) hmarg
  have hStarNN : ∀ W aa xx, 0 ≤ D.evenStar q W aa xx := by
    intro W aa xx
    unfold Ctx.evenStar
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg
    · exact Finset.prod_nonneg fun j _ =>
        (hP q W (cellOf η₀ (cubeFlip aa.1 j))).1 (y j)
    · apply mul_nonneg
      · split_ifs <;> norm_num
      · exact mul_nonneg (Nat.cast_nonneg _) (hRowNN W aa y xx)
  by_cases hl0 : l = 0
  · subst l
    have hpoint (W : D.Anch) :
        (D.anchorLaw q).w W *
          (if D.GoodPre q W then
            ∑ f, (J W).w f * ∏ i : Fin 0, (D.N : ℝ) * D.evenRow q W f (a i) x else 0) ≤
          (D.anchorLaw q).w W := by
      by_cases hg : D.GoodPre q W
      · simp [hg, (J W).sum_eq_one]
      · simpa [hg] using (D.anchorLaw q).nonneg W
    calc
      ∑ W, (D.anchorLaw q).w W *
          (if D.GoodPre q W then
            ∑ f, (J W).w f * ∏ i : Fin 0, (D.N : ℝ) * D.evenRow q W f (a i) x else 0) ≤
        ∑ W, (D.anchorLaw q).w W := Finset.sum_le_sum fun W _ => hpoint W
      _ = 1 := (D.anchorLaw q).sum_eq_one
      _ = (4 : ℝ) ^ 0 * ∏ i : Fin 0, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x := by simp
  · have hlpos : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl0
    have hStarProdNN : ∀ W, 0 ≤ ∏ i : Fin l, D.evenStar q W (a i) x := by
      intro W
      exact Finset.prod_nonneg fun i _ => hStarNN W (a i) x
    have hMeanProdNN : 0 ≤ ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x := by
      exact Finset.prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
        ((D.Usel q (cellOf η₀ (a i).1)).nonneg x)
    have hpoint (W : D.Anch) :
        (if D.GoodPre q W then
          ∑ f, (J W).w f * ∏ i : Fin l, (D.N : ℝ) * D.evenRow q W f (a i) x else 0) ≤
        2 * (if D.GoodPre q W then ∏ i : Fin l, D.evenStar q W (a i) x else 0) := by
      by_cases hg : D.GoodPre q W
      · simpa [hg] using hfac W hg x l hl a hsep
      · simp [hg]
    have hdrop :
        (∑ W, (D.anchorLaw q).w W *
          (if D.GoodPre q W then ∏ i : Fin l, D.evenStar q W (a i) x else 0)) ≤
        ∑ W, (D.anchorLaw q).w W * ∏ i : Fin l, D.evenStar q W (a i) x := by
      apply Finset.sum_le_sum
      intro W hW
      by_cases hg : D.GoodPre q W
      · simp [hg]
      · simpa [hg] using mul_nonneg ((D.anchorLaw q).nonneg W) (hStarProdNN W)
    have hpow : (2 : ℝ) * (2 : ℝ) ^ l ≤ (4 : ℝ) ^ l := by
      have hexp : l + 1 ≤ 2 * l := by omega
      calc
        (2 : ℝ) * (2 : ℝ) ^ l = (2 : ℝ) ^ (l + 1) := by rw [pow_succ]; ring
        _ ≤ (2 : ℝ) ^ (2 * l) := pow_le_pow_right₀ (by norm_num) hexp
        _ = (4 : ℝ) ^ l := by rw [pow_mul]; norm_num
    calc
      ∑ W, (D.anchorLaw q).w W *
          (if D.GoodPre q W then
            ∑ f, (J W).w f * ∏ i : Fin l, (D.N : ℝ) * D.evenRow q W f (a i) x else 0) ≤
        ∑ W, (D.anchorLaw q).w W *
          (2 * (if D.GoodPre q W then ∏ i : Fin l, D.evenStar q W (a i) x else 0)) := by
            apply Finset.sum_le_sum
            intro W hW
            exact mul_le_mul_of_nonneg_left (hpoint W) ((D.anchorLaw q).nonneg W)
      _ = 2 * ∑ W, (D.anchorLaw q).w W *
            (if D.GoodPre q W then ∏ i : Fin l, D.evenStar q W (a i) x else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro W hW
              ring
      _ ≤ 2 * ∑ W, (D.anchorLaw q).w W * ∏ i : Fin l, D.evenStar q W (a i) x :=
            mul_le_mul_of_nonneg_left hdrop (by norm_num)
      _ ≤ 2 * ((2 : ℝ) ^ l * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x) :=
            mul_le_mul_of_nonneg_left (hint x l hl a hsep) (by norm_num)
      _ ≤ (4 : ℝ) ^ l * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x := by
            calc
              2 * ((2 : ℝ) ^ l * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x) =
                  (2 * (2 : ℝ) ^ l) * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x := by ring
              _ ≤ (4 : ℝ) ^ l * ∏ i : Fin l, (D.N : ℝ) * (D.Usel q (cellOf η₀ (a i).1)).w x :=
                mul_le_mul_of_nonneg_right hpow hMeanProdNN

set_option maxHeartbeats 1000000 in
/-- L8.1l(viii) (08:450–454): Lemma 3.6 with labels for the even rows at a fixed successful history with the
selected-anchor load bound: near roles have residual words within distance four (fraction at most
`2(n+1)^4 2^{-(n-m)}`), the cap is `e^{.1n}` on predictive success, `n f e^{.1n} ≤ 1`, the comparison means are
the selected laws (average at most `C_L`), separated moments are at most `4^l ∏ N U(x)`; so the normalized even load
exceeds `16(C_L + 1)` with probability at most `n 2^n 4^{-n}`, and otherwise the column sums are at most
`2^{n-1} 16(C_L + 1)/N ≤ 1`. -/
theorem even_tail (CL : ℝ) (hCL : 0 ≤ CL) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → D.N ≤ D.n * 2 ^ D.n →
      16 * (CL + 1) * 2 ^ D.n ≤ D.N → D.EvenRowCap → D.PRowFacts → D.SelConseq →
      ∀ q : D.Pre, D.Good q → D.LoadOK CL q →
        ∀ J : D.Anch → FinProb (OddRole D.n → Fin D.N), (∀ W, D.GoodPre q W → D.ClockOK q W (J W)) →
          D.EvenMoment q J →
          ∑ W, (D.anchorLaw q).w W *
              (if D.GoodPre q W then (J W).pr (fun f => ∃ x, 1 < D.evenCol q W f x) else 0) ≤
            (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  classical
  let b : ℝ := Real.log 2 / 2 - (1 / 10 : ℝ)
  have hb : 0 < b := by
    dsimp [b]
    nlinarith [Real.log_two_gt_d9]
  have hdecay : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) ^ (5 : ℕ) * Real.exp (-b * (n : ℝ)))
      Filter.atTop (nhds 0) :=
    by
      simpa [Function.comp_def] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 : ℝ) b hb).comp
          tendsto_natCast_atTop_atTop
  have hsmallEv : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ (5 : ℕ) * Real.exp (-b * (n : ℝ)) < (1 / 10 : ℝ) :=
    hdecay.eventually (Iio_mem_nhds (by norm_num))
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp hsmallEv
  have hFresBound (n : ℕ) (hG : GridFacts η₀ n) :
      fRes η₀ n 4 ≤ 10 * (n : ℝ) ^ (4 : ℕ) *
        Real.exp (-((n : ℝ) / 2 * Real.log 2)) := by
    let d := dC η₀ n
    have hdle : (d : ℝ) ≤ n := by simpa [d] using hG.hd_ok.2.2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hG.pos.1
    have hchoose (j : ℕ) (hj : j ∈ Finset.range 5) :
        (Nat.choose d j : ℝ) ≤ (n : ℝ) ^ 4 := by
      have hj4 : j ≤ 4 := by simp only [Finset.mem_range] at hj; omega
      have hnat := Nat.choose_le_pow d j
      have hr : (Nat.choose d j : ℝ) ≤ (d : ℝ) ^ j := by exact_mod_cast hnat
      calc
        (Nat.choose d j : ℝ) ≤ (d : ℝ) ^ j := hr
        _ ≤ (n : ℝ) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hdle j
        _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ hn1 (by exact_mod_cast hj4)
    have hsum : (∑ j ∈ Finset.range 5, (Nat.choose d j : ℝ)) ≤ 5 * (n : ℝ) ^ 4 := by
      calc
        (∑ j ∈ Finset.range 5, (Nat.choose d j : ℝ)) ≤
            ∑ j ∈ Finset.range 5, (n : ℝ) ^ 4 :=
              Finset.sum_le_sum fun j hj => hchoose j hj
        _ = 5 * (n : ℝ) ^ 4 := by simp
    have hpowEq : (2 : ℝ) ^ d = Real.exp ((d : ℝ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] <;> ring
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hdhalf : (n : ℝ) / 2 ≤ d := by nlinarith [hG.hd_ok.2.1]
    have hdenLower : Real.exp ((n : ℝ) / 2 * Real.log 2) ≤ (2 : ℝ) ^ d := by
      rw [hpowEq]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hdhalf (le_of_lt hlog2pos))
    have hdenPos : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) _
    unfold fRes
    calc
      2 * (∑ j ∈ Finset.range 5, (Nat.choose d j : ℝ)) / (2 : ℝ) ^ d ≤
          (10 * (n : ℝ) ^ 4) / (2 : ℝ) ^ d := by
            apply div_le_div_of_nonneg_right _ hdenPos.le
            calc
              2 * (∑ j ∈ Finset.range 5, (Nat.choose d j : ℝ)) ≤
                  2 * (5 * (n : ℝ) ^ 4) := mul_le_mul_of_nonneg_left hsum (by norm_num)
              _ = 10 * (n : ℝ) ^ 4 := by ring
      _ ≤ (10 * (n : ℝ) ^ 4) / Real.exp ((n : ℝ) / 2 * Real.log 2) :=
            div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hdenLower
      _ = 10 * (n : ℝ) ^ 4 * Real.exp (-((n : ℝ) / 2 * Real.log 2)) := by
            rw [div_eq_mul_inv, ← Real.exp_neg]
  refine ⟨max n₁ 2, ?_⟩
  intro D hn hG hNupper hNlower hRowCap hP hSel q hq hLoad J hClock hMoment
  have hn₁D : n₁ ≤ D.n := le_trans (le_max_left _ _) hn
  have hn₂D : 2 ≤ D.n := le_trans (le_max_right _ _) hn
  have hsmall : (D.n : ℝ) * fRes η₀ D.n 4 *
      Real.exp ((1 / 10 : ℝ) * D.n) ≤ 1 := by
    have hfr := hFresBound D.n hG
    have hdec := hn₁ D.n hn₁D
    calc
      (D.n : ℝ) * fRes η₀ D.n 4 * Real.exp ((1 / 10 : ℝ) * D.n) ≤
          (D.n : ℝ) * (10 * (D.n : ℝ) ^ (4 : ℕ) *
            Real.exp (-((D.n : ℝ) / 2 * Real.log 2))) * Real.exp ((1 / 10 : ℝ) * D.n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfr (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _ = 10 * (D.n : ℝ) ^ (5 : ℕ) * Real.exp (-b * (D.n : ℝ)) := by
          calc
            _ = 10 * (D.n : ℝ) ^ (5 : ℕ) *
                (Real.exp (-((D.n : ℝ) / 2 * Real.log 2)) *
                  Real.exp ((1 / 10 : ℝ) * D.n)) := by ring
            _ = 10 * (D.n : ℝ) ^ (5 : ℕ) * Real.exp (-b * (D.n : ℝ)) := by
                  have hexp :
                      Real.exp (-((D.n : ℝ) / 2 * Real.log 2)) *
                        Real.exp ((1 / 10 : ℝ) * D.n) = Real.exp (-b * (D.n : ℝ)) := by
                    calc
                      _ = Real.exp (-((D.n : ℝ) / 2 * Real.log 2) + (1 / 10 : ℝ) * D.n) :=
                        (Real.exp_add _ _).symm
                      _ = _ := congrArg Real.exp (by dsimp [b]; ring)
                  rw [hexp]
      _ ≤ 1 := by nlinarith [hdec]
  let Ω := D.Anch × (OddRole D.n → Fin D.N)
  let P : FinProb Ω := FinProb.bind (D.anchorLaw q) J
  let succ : Finset Ω := Finset.univ.filter fun ω => D.GoodPre q ω.1
  let Z : EvenRole D.n → Fin D.N → Ω → ℝ := fun a' z ω =>
    if D.GoodPre q ω.1 ∧ (J ω.1).w ω.2 ≠ 0 then
      (D.N : ℝ) * D.evenRow q ω.1 ω.2 a' z else 0
  let d : EvenRole D.n → Fin D.N → ℝ := fun a' z =>
    (D.N : ℝ) * (D.Usel q (cellOf η₀ a'.1)).w z
  let near : EvenRole D.n → Finset (EvenRole D.n) := fun a' => evenResNear η₀ 4 a'
  let L : ℝ := Real.exp ((1 / 10 : ℝ) * D.n)
  haveI : Nonempty (EvenRole D.n) := by
    have hcard : 0 < Fintype.card (EvenRole D.n) := by
      rw [hG.even_card]
      exact Nat.pow_pos (by norm_num)
    exact Fintype.card_pos_iff.mp hcard
  have hRowLaw := evenRow_law η₀ β p h D hG hP
  have hZnonneg : ∀ a' z ω, 0 ≤ Z a' z ω := by
    intro a' z ω
    by_cases hg : D.GoodPre q ω.1
    · by_cases hw : (J ω.1).w ω.2 = 0
      · simp [Z, hg, hw]
      · have hclock := hClock ω.1 hg
        have hsuccess := (hclock.1 ω.2 hw).2 a'
        have hrow := hRowLaw q ω.1 ω.2 a' hsuccess
        simp [Z, hg, hw]
        exact mul_nonneg (Nat.cast_nonneg _) (hrow.1 z)
    · simp [Z, hg]
  have hLnonneg : 0 ≤ L := by positivity
  have hZcap : ∀ a' z ω, ω ∈ succ → Z a' z ω ≤ L := by
    intro a' z ω hω
    have hg : D.GoodPre q ω.1 := by simpa [succ] using hω
    by_cases hw : (J ω.1).w ω.2 = 0
    · simp [Z, hg, hw]
      positivity
    · have hclock := hClock ω.1 hg
      have hsuccess := (hclock.1 ω.2 hw).2 a'
      have hcap := hRowCap q ω.1 a' (nbrLabels ω.2 a') hq hsuccess z
      have hcond : D.GoodPre q ω.1 ∧ (J ω.1).w ω.2 ≠ 0 := ⟨hg, hw⟩
      change (if D.GoodPre q ω.1 ∧ (J ω.1).w ω.2 ≠ 0 then
        (D.N : ℝ) * D.evenRow q ω.1 ω.2 a' z else 0) ≤ L
      rw [if_pos hcond]
      simpa [L, Ctx.evenRow] using hcap
  have hnearSelf : ∀ a' : EvenRole D.n, a' ∈ near a' := by
    intro a'
    simp [near, evenResNear]
  have hfNonneg : 0 ≤ fRes η₀ D.n 4 := by
    unfold fRes
    positivity
  have hnearCard : ∀ a' : EvenRole D.n,
      ((near a').card : ℝ) ≤ fRes η₀ D.n 4 * Fintype.card (EvenRole D.n) := by
    intro a'
    exact hG.res_near 4 a'
  have hCon := hSel q hq.2
  have hdNonneg (a' : EvenRole D.n) (z : Fin D.N) : 0 ≤ d a' z := by
    exact mul_nonneg (Nat.cast_nonneg _) ((D.Usel q (cellOf η₀ a'.1)).nonneg z)
  have hloadEq (a' : EvenRole D.n) (z : Fin D.N) :
      d a' z = D.selLoad q (cellOf η₀ a'.1) z := by
    obtain ⟨ℓ, hℓ⟩ := Option.isSome_iff_exists.mp (hCon.1 (cellOf η₀ a'.1))
    simp [d, Ctx.selLoad, Ctx.selTag, Ctx.Usel, hℓ]
  have hmean : ∀ z : Fin D.N,
      (Fintype.card (EvenRole D.n) : ℝ)⁻¹ * ∑ a' : EvenRole D.n, d a' z ≤ CL := by
    intro z
    calc
      (Fintype.card (EvenRole D.n) : ℝ)⁻¹ * ∑ a' : EvenRole D.n, d a' z =
          (Fintype.card (EvenRole D.n) : ℝ)⁻¹ *
            ∑ a' : EvenRole D.n, D.selLoad q (cellOf η₀ a'.1) z := by
              congr 1
              apply Finset.sum_congr rfl
              intro a' ha'
              exact hloadEq a' z
      _ ≤ CL := hLoad z
  have hselCap : Fintype.card (EvenRole D.n) > 0 := by
    rw [hG.even_card]
    exact Nat.pow_pos (by norm_num)
  have hNpos : 0 < (D.N : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 16 * (CL + 1) * (2 : ℝ) ^ D.n) hNlower
  have hcardCast : (Fintype.card (EvenRole D.n) : ℝ) = (2 : ℝ) ^ (D.n - 1) := by
    exact_mod_cast hG.even_card
  have hpow : (2 : ℝ) ^ D.n = 2 * (2 : ℝ) ^ (D.n - 1) := by
    have heq : D.n - 1 + 1 = D.n := Nat.sub_add_cancel (by omega)
    calc
      (2 : ℝ) ^ D.n = (2 : ℝ) ^ (D.n - 1 + 1) := congrArg (fun n : ℕ => (2 : ℝ) ^ n) heq.symm
      _ = (2 : ℝ) ^ (D.n - 1) * 2 := by rw [pow_succ]
      _ = 2 * (2 : ℝ) ^ (D.n - 1) := by ring
  have hNscaled : 32 * (CL + 1) * (Fintype.card (EvenRole D.n) : ℝ) ≤ D.N := by
    calc
      32 * (CL + 1) * (Fintype.card (EvenRole D.n) : ℝ) =
          16 * (CL + 1) * (2 : ℝ) ^ D.n := by rw [hcardCast, hpow]; ring
      _ ≤ D.N := hNlower
  have hNratio : 32 * (CL + 1) ≤
      (D.N : ℝ) / (Fintype.card (EvenRole D.n) : ℝ) :=
    (le_div_iff₀ (Nat.cast_pos.mpr hselCap)).2 hNscaled
  have hRatioPos : 0 < (D.N : ℝ) / (Fintype.card (EvenRole D.n) : ℝ) :=
    div_pos hNpos (Nat.cast_pos.mpr hselCap)
  have hEqProb :
      ∑ W, (D.anchorLaw q).w W *
          (if D.GoodPre q W then (J W).pr (fun f => ∃ z, 1 < D.evenCol q W f z) else 0) =
        P.pr (fun ω => D.GoodPre q ω.1 ∧ ∃ z, 1 < D.evenCol q ω.1 ω.2 z) := by
    have hbind (A : D.Anch × (OddRole D.n → Fin D.N) → Prop) :
        P.pr A = ∑ W, (D.anchorLaw q).w W * (J W).pr (fun f => A (W, f)) := by
      change (∑ ω : D.Anch × (OddRole D.n → Fin D.N),
          if A ω then (D.anchorLaw q).w ω.1 * (J ω.1).w ω.2 else 0) = _
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro W hW
      calc
        (∑ f, if A (W, f) then (D.anchorLaw q).w W * (J W).w f else 0) =
            ∑ f, (D.anchorLaw q).w W * (if A (W, f) then (J W).w f else 0) := by
              apply Finset.sum_congr rfl
              intro f hf
              by_cases hA : A (W, f) <;> simp [hA]
        _ = (D.anchorLaw q).w W * ∑ f, if A (W, f) then (J W).w f else 0 := by
              rw [Finset.mul_sum]
        _ = (D.anchorLaw q).w W * (J W).pr (fun f => A (W, f)) := rfl
    rw [hbind]
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hg : D.GoodPre q W
    · simp only [if_pos hg]
      congr 1
      apply congrArg (fun A : (OddRole D.n → Fin D.N) → Prop => (J W).pr A)
      funext f
      simp [hg]
    · simp [hg, FinProb.pr]
  let high : Ω → Prop := fun ω => ω ∈ succ ∧ ∃ z : Fin D.N,
    16 * (CL + 1) < (Fintype.card (EvenRole D.n) : ℝ)⁻¹ *
      ∑ a' : EvenRole D.n, Z a' z ω
  have hHigh : ∀ W f z, D.GoodPre q W → (J W).w f ≠ 0 →
      1 < D.evenCol q W f z →
      16 * (CL + 1) < (Fintype.card (EvenRole D.n) : ℝ)⁻¹ *
        ∑ a' : EvenRole D.n, Z a' z (W, f) := by
    intro W f z hg hw hcol
    have hZeq : ∀ a' : EvenRole D.n, Z a' z (W, f) =
        (D.N : ℝ) * D.evenRow q W f a' z := by
      intro a'
      have hcond : D.GoodPre q W ∧ (J W).w f ≠ 0 := ⟨hg, hw⟩
      simp [Z, hcond]
    have hsumEq : ∑ a' : EvenRole D.n, Z a' z (W, f) =
        (D.N : ℝ) * D.evenCol q W f z := by
      simp_rw [hZeq]
      unfold Ctx.evenCol
      exact (Finset.mul_sum Finset.univ (fun a' => D.evenRow q W f a' z) (D.N : ℝ)).symm
    have hCLpos : 0 < CL + 1 := by linarith [hCL]
    have hlarge : 16 * (CL + 1) <
        ((D.N : ℝ) / (Fintype.card (EvenRole D.n) : ℝ)) * D.evenCol q W f z := by
      calc
        16 * (CL + 1) < 32 * (CL + 1) := by nlinarith
        _ ≤ (D.N : ℝ) / (Fintype.card (EvenRole D.n) : ℝ) := hNratio
        _ < ((D.N : ℝ) / (Fintype.card (EvenRole D.n) : ℝ)) * D.evenCol q W f z := by
              calc
                _ = _ * 1 := by ring
                _ < _ * D.evenCol q W f z := mul_lt_mul_of_pos_left hcol hRatioPos
    rw [hsumEq]
    calc
      16 * (CL + 1) <
          ((D.N : ℝ) / (Fintype.card (EvenRole D.n) : ℝ)) * D.evenCol q W f z := hlarge
      _ = (Fintype.card (EvenRole D.n) : ℝ)⁻¹ *
            ((D.N : ℝ) * D.evenCol q W f z) := by ring
  have hprob_le :
      P.pr (fun ω => D.GoodPre q ω.1 ∧ ∃ z, 1 < D.evenCol q ω.1 ω.2 z) ≤ P.pr high := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω hω
    by_cases he : D.GoodPre q ω.1 ∧ ∃ z, 1 < D.evenCol q ω.1 ω.2 z
    · by_cases hwP : P.w ω = 0
      · simp [he, hwP]
      · rcases he with ⟨hg, ⟨z, hcol⟩⟩
        have hwJ : (J ω.1).w ω.2 ≠ 0 := by
          intro hz
          apply hwP
          simp [P, FinProb.bind, hz]
        have hlarge := hHigh ω.1 ω.2 z hg hwJ hcol
        have htarget : D.GoodPre q ω.1 ∧ ∃ z, 1 < D.evenCol q ω.1 ω.2 z :=
          ⟨hg, ⟨z, hcol⟩⟩
        have hmem : ω ∈ succ := by simp [succ, hg]
        have hhi : high ω := ⟨hmem, ⟨z, hlarge⟩⟩
        rw [if_pos htarget, if_pos hhi] <;> rfl
    · rw [if_neg he]
      by_cases hh : high ω
      · rw [if_pos hh]
        exact P.nonneg ω
      · rw [if_neg hh]
  have hlabels : (Fintype.card (Fin D.N) : ℝ) ≤ (D.n : ℝ) * 2 ^ D.n := by
    simpa using (show (D.N : ℝ) ≤ (D.n : ℝ) * (2 : ℝ) ^ D.n by exact_mod_cast hNupper)
  have hsepRoles {m : ℕ} (s : Fin m → EvenRole D.n)
      (hsep : ∀ i j : Fin m, j < i → s i ∉ near (s j)) :
      ∀ i j, i ≠ j → 4 < _root_.hammingDist (resOf η₀ (s i).1) (resOf η₀ (s j).1) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hji
    · have hnot := hsep j i hijlt
      have hdist : ¬ _root_.hammingDist (resOf η₀ (s i).1) (resOf η₀ (s j).1) ≤ 4 := by
        intro hle
        apply hnot
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hammingDist_comm] using hle⟩
      exact Nat.lt_of_not_ge hdist
    · have hnot := hsep i j hji
      have hdist : ¬ _root_.hammingDist (resOf η₀ (s i).1) (resOf η₀ (s j).1) ≤ 4 := by
        intro hle
        apply hnot
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
      exact Nat.lt_of_not_ge hdist
  have hJointEq (z : Fin D.N) (m : ℕ) (s : Fin m → EvenRole D.n) :
      (∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) z ω) =
        ∑ W, (D.anchorLaw q).w W *
          (if D.GoodPre q W then
            ∑ f, (J W).w f * ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z else 0) := by
    have hfilter (s : Finset Ω) (g : Ω → ℝ) :
        (∑ ω ∈ s, g ω) = ∑ ω, if ω ∈ s then g ω else 0 := by
      simpa using (Finset.sum_ite_mem_eq s g).symm
    have hmem (ω : Ω) : ω ∈ succ ↔ D.GoodPre q ω.1 := by
      simp only [succ, Finset.mem_filter, Finset.mem_univ, true_and]
    have hsuccFilter (g : Ω → ℝ) :
        (∑ ω ∈ succ, g ω) = ∑ ω, if D.GoodPre q ω.1 then g ω else 0 := by
      calc
        (∑ ω ∈ succ, g ω) = ∑ ω, if ω ∈ succ then g ω else 0 := hfilter succ g
        _ = ∑ ω, if D.GoodPre q ω.1 then g ω else 0 := by
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hg : D.GoodPre q ω.1
          · simp [hg, hmem ω]
          · simp [hg, hmem ω]
    have hpoint (W : D.Anch) (f : OddRole D.n → Fin D.N) :
        (if D.GoodPre q W then P.w (W, f) * ∏ i, Z (s i) z (W, f) else 0) =
          (if D.GoodPre q W then
            (D.anchorLaw q).w W * (J W).w f *
              ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z else 0) := by
      by_cases hg : D.GoodPre q W
      · simp only [if_pos hg]
        have hp : P.w (W, f) = (D.anchorLaw q).w W * (J W).w f := rfl
        rw [hp]
        by_cases hw : (J W).w f = 0
        · simp [Z, hg, hw]
        · simp [Z, hg, hw]
      · simp [hg]
    calc
      (∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) z ω) =
          ∑ ω, if D.GoodPre q ω.1 then P.w ω * ∏ i, Z (s i) z ω else 0 := hsuccFilter _
      _ = ∑ W, ∑ f, if D.GoodPre q W then
            ((D.anchorLaw q).w W * (J W).w f) *
              ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z else 0 := by
                rw [Fintype.sum_prod_type]
                apply Finset.sum_congr rfl
                intro W hW
                apply Finset.sum_congr rfl
                intro f hf
                simpa [mul_assoc] using hpoint W f
      _ = ∑ W, (D.anchorLaw q).w W *
            (if D.GoodPre q W then
              ∑ f, (J W).w f * ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z else 0) := by
              apply Finset.sum_congr rfl
              intro W hW
              by_cases hg : D.GoodPre q W
              · simp only [if_pos hg]
                calc
                  ∑ f, ((D.anchorLaw q).w W * (J W).w f) *
                      ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z =
                    ∑ f, (D.anchorLaw q).w W *
                      ((J W).w f * ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z) := by
                        apply Finset.sum_congr rfl
                        intro f hf
                        ring
                  _ = (D.anchorLaw q).w W *
                      ∑ f, (J W).w f * ∏ i, (D.N : ℝ) * D.evenRow q W f (s i) z := by
                        rw [← Finset.mul_sum]
              · simp [hg]
  have hjoint : ∀ z (m : ℕ), m ≤ D.n → ∀ s : Fin m → EvenRole D.n,
      (∀ i j : Fin m, j < i → s i ∉ near (s j)) →
        ∑ ω ∈ succ, P.w ω * ∏ i, Z (s i) z ω ≤ 4 ^ m * ∏ i, d (s i) z := by
    intro z m hm s hsep
    rw [hJointEq z m s]
    exact hMoment z m hm s (hsepRoles s hsep)
  have htail := HypercubeRamsey.scatteredMoments_union_labels
    P succ Z hZnonneg L hLnonneg hZcap near hnearSelf (fRes η₀ D.n 4) hfNonneg hnearCard
    D.n (by omega) 4 CL (by norm_num) hCL d hdNonneg hmean hjoint hsmall hlabels
  let target : Ω → Prop := fun ω =>
    D.GoodPre q ω.1 ∧ ∃ z, 1 < D.evenCol q ω.1 ω.2 z
  have hbindPr (A : Ω → Prop) :
      P.pr A = ∑ W, (D.anchorLaw q).w W * (J W).pr (fun f => A (W, f)) := by
    change (∑ ω : D.Anch × (OddRole D.n → Fin D.N),
        if A ω then (D.anchorLaw q).w ω.1 * (J ω.1).w ω.2 else 0) = _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro W hW
    calc
      (∑ f, if A (W, f) then (D.anchorLaw q).w W * (J W).w f else 0) =
          ∑ f, (D.anchorLaw q).w W * (if A (W, f) then (J W).w f else 0) := by
            apply Finset.sum_congr rfl
            intro f hf
            by_cases hA : A (W, f) <;> simp [hA]
      _ = (D.anchorLaw q).w W * ∑ f, if A (W, f) then (J W).w f else 0 := by
            rw [Finset.mul_sum]
      _ = (D.anchorLaw q).w W * (J W).pr (fun f => A (W, f)) := rfl
  have hTargetEq :
      ∑ W, (D.anchorLaw q).w W *
          (if D.GoodPre q W then (J W).pr (fun f => ∃ z, 1 < D.evenCol q W f z) else 0) =
        P.pr target := by
    rw [hbindPr target]
    apply Finset.sum_congr rfl
    intro W hW
    by_cases hg : D.GoodPre q W
    · simp [target, hg]
    · simp only [target, if_neg hg]
      have hpr : (J W).pr (fun f => D.GoodPre q W ∧ ∃ z, 1 < D.evenCol q W f z) = 0 := by
        unfold FinProb.pr
        simp [hg]
      rw [hpr]
  have hTargetLe : P.pr target ≤ P.pr high := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro ω hω
    by_cases ht : target ω
    · by_cases hw : P.w ω = 0
      · simp [ht, hw]
      · rcases ht with ⟨hg, ⟨z, hcol⟩⟩
        have hwJ : (J ω.1).w ω.2 ≠ 0 := by
          intro hz
          apply hw
          simp [P, FinProb.bind, hz]
        have hlarge := hHigh ω.1 ω.2 z hg hwJ hcol
        have htarget : target ω := ⟨hg, ⟨z, hcol⟩⟩
        have hmem : ω ∈ succ := by simp [succ, hg]
        have hhi : high ω := ⟨hmem, ⟨z, hlarge⟩⟩
        rw [if_pos htarget, if_pos hhi] <;> rfl
    · rw [if_neg ht]
      by_cases hh : high ω
      · rw [if_pos hh]
        exact P.nonneg ω
      · rw [if_neg hh]
  have htailBound : P.pr high ≤
      (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
    have hnum : (4 : ℝ) * 4 = 16 := by norm_num
    rw [hnum] at htail
    simpa [high, FinProb.pr, mul_assoc, mul_left_comm, mul_comm] using htail
  calc
    ∑ W, (D.anchorLaw q).w W *
        (if D.GoodPre q W then (J W).pr (fun f => ∃ z, 1 < D.evenCol q W f z) else 0) =
        P.pr target := hTargetEq
    _ ≤ P.pr high := hTargetLe
    _ ≤ (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := htailBound

end Nodes

end HypercubeRamsey.S08
