import HypercubeRamsey.S11.Core.Definitions
import HypercubeRamsey.S03.GatedPosterior
import HypercubeRamsey.S11.Core.Slice_q_s11_slice
import HypercubeRamsey.S11.Core.SliceSigmaMain_q_s11_slice

/-!
# Proposition 11.1: the biased menu and the slice experiment

Source: `sections/11-…tex`, lines 26–89 (P11.1-menu, P11.1a, P11.1b in `research/blueprint/PART-B.md` §3.11).
-/

namespace HypercubeRamsey.S11.Core

open HypercubeRamsey OAI.HypercubeRamsey
open Classical
open Filter
open scoped BigOperators

/-- P11.1-menu (11:26–33).  Availability of `PBias(n^.01, .01n, h₀)` at tolerance `κ` gives availability of one
colour sign at tolerance `κ/2` (F-UnionAvail: two bad removal pairs of size `κN/2` would combine into one of size
`κN`).  For a witness `(μ, ν)` of colour `G`, `E_ν d_G(μ, y) ≥ 1/2 + n^{-h₀}` and `d_G ≤ 1`, so the columns of
degree at least `1/2 + 2g` carry `ν`-mass at least `2(n^{-h₀} - 2g) ≥ n^{-h₀}` (as `h₀ < .01`); conditioning `ν`
on them costs at most `h₀ log n ≤ .001 n` width.  Index the menu by the removal pairs of size at most `κN/2` and
choose one restricted witness for each. -/
theorem biased_menu (h₀ κ : ℝ) (hh₀ : 0 < h₀) (hh₀' : h₀ < 1 / 100) (hκ : 0 < κ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)},
      AvailableAt κ (PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) h₀).toPatch n N E X Y →
      Nonempty (Menu11 n N E X Y (κ / 2)) := by
  classical
  have hlogLimit : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  have hlogSmall : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ (1 / 10 : ℝ) * n := by
    have hev := hlogLimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10))
    filter_upwards [hev, (eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hratio hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hratio' : Real.log (n : ℝ) / (n : ℝ) < 1 / 10 := hratio
    exact le_of_lt ((div_lt_iff₀ hnpos).mp hratio')
  have hlogCost : ∀ᶠ n : ℕ in atTop,
      h₀ * Real.log (n : ℝ) ≤ (1 / 1000 : ℝ) * n := by
    filter_upwards [hlogSmall, (eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hlog hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hlogNonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have h₀Bound := mul_le_mul_of_nonneg_right (le_of_lt hh₀') hlogNonneg
    have hlogBound := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 1 / 100)
    nlinarith
  have hgap : 0 < (1 / 100 : ℝ) - h₀ := by linarith
  have hlargeGap : ∀ᶠ n : ℕ in atTop,
      4 ≤ (n : ℝ) ^ ((1 / 100 : ℝ) - h₀) := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 / 100 : ℝ) - h₀)) atTop atTop :=
      (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop 4
  obtain ⟨nlog, hnlog⟩ := Filter.eventually_atTop.1 hlogCost
  obtain ⟨ngap, hngap⟩ := Filter.eventually_atTop.1 hlargeGap
  have hheavy_mass {n N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour)
      (μ ν : Law N) (hbias : (n : ℝ) ^ (-h₀) ≤ dens E G μ ν - 1 / 2)
      (hn : 2 ≤ n) (hcost : h₀ * Real.log (n : ℝ) ≤ (1 / 1000 : ℝ) * n)
      (hgapn : 4 ≤ (n : ℝ) ^ ((1 / 100 : ℝ) - h₀)) :
      (n : ℝ) ^ (-h₀) ≤
        ∑ y ∈ (Finset.univ.filter fun y =>
          1 / 2 + 2 * gS n ≤ colDeg E G μ y), ν.w y := by
    classical
    let H := Finset.univ.filter fun y : Fin N => 1 / 2 + 2 * gS n ≤ colDeg E G μ y
    let b : ℝ := (n : ℝ) ^ (-h₀)
    let t : ℝ := 1 / 2 + 2 * gS n
    let q : ℝ := 1 / 2 - 2 * gS n
    let mass : ℝ := ∑ y, if y ∈ H then ν.w y else 0
    let rest : ℝ := ∑ y, if y ∉ H then ν.w y else 0
    have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hbpos : 0 < b := by dsimp [b]; positivity
    have hbsmall : 4 * gS n ≤ b := by
      have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hnreal
      have hmul : (n : ℝ) ^ (-(1 : ℝ) / 100) *
          (n : ℝ) ^ ((1 / 100 : ℝ) - h₀) = b := by
        dsimp [b]
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      have hscaled := mul_le_mul_of_nonneg_left hgapn
        (Real.rpow_nonneg hnpos.le (-(1 : ℝ) / 100))
      unfold gS
      rw [← hmul]
      nlinarith
    have hbLt : b < 1 := by
      dsimp [b]
      exact Real.rpow_lt_one_of_one_lt_of_neg hnreal (by linarith)
    have hqpos : 0 < q := by dsimp [q]; nlinarith [hbsmall, hbLt]
    have hgh : 0 ≤ gS n := by unfold gS; positivity
    have hqle : q ≤ 1 / 2 := by dsimp [q]; linarith [hgh]
    have hdegNonneg (y : Fin N) : 0 ≤ colDeg E G μ y := by
      unfold colDeg
      apply Finset.sum_nonneg
      intro x hx
      apply mul_nonneg (μ.nonneg x)
      by_cases h : Hits E G x y <;> simp [hit, h]
    have hdegLe (y : Fin N) : colDeg E G μ y ≤ 1 := by
      unfold colDeg
      calc
        (∑ x, μ.w x * hit E G x y) ≤ ∑ x, μ.w x * 1 := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_left (by
            unfold hit
            split_ifs <;> norm_num) (μ.nonneg x)
        _ = 1 := by simp [μ.sum_eq_one]
    have hdens : dens E G μ ν = ∑ y, ν.w y * colDeg E G μ y := by
      unfold dens
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [colDeg]
      calc
        (∑ x, μ.w x * ν.w y * (if Hits E G x y then 1 else 0)) =
            ∑ x, ν.w y * (μ.w x * (if Hits E G x y then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
        _ = ν.w y * ∑ x, μ.w x * (if Hits E G x y then 1 else 0) := by
          exact (Finset.mul_sum Finset.univ
            (fun x => μ.w x * (if Hits E G x y then 1 else 0)) (ν.w y)).symm
    have hmassSplit :
        (∑ y, ν.w y) = mass + rest := by
      dsimp [mass, rest]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hmem : y ∈ H <;> simp [hmem]
    have hrest : rest = 1 - mass := by
      have hs := hmassSplit
      rw [ν.sum_eq_one] at hs
      linarith
    have hupper : dens E G μ ν ≤ t + q * mass := by
      rw [hdens]
      calc
        (∑ y, ν.w y * colDeg E G μ y) ≤
            ∑ y, ν.w y * (if y ∈ H then 1 else t) := by
          apply Finset.sum_le_sum
          intro y hy
          apply mul_le_mul_of_nonneg_left _ (ν.nonneg y)
          by_cases hmem : y ∈ H
          · simp [hmem]
            exact hdegLe y
          · have hnotdeg : ¬ t ≤ colDeg E G μ y := by
              intro hle
              apply hmem
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
            simpa [hmem] using (le_of_lt (lt_of_not_ge hnotdeg))
        _ = mass + t * rest := by
          calc
            (∑ y, ν.w y * (if y ∈ H then 1 else t)) =
                ∑ y, ((if y ∈ H then ν.w y else 0) +
                  t * (if y ∉ H then ν.w y else 0)) := by
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hmem : y ∈ H <;> simp [hmem] <;> ring
            _ = mass + t * rest := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = t + q * mass := by
          rw [hrest]
          dsimp [t, q]
          ring
    have hineq : b - 2 * gS n ≤ q * mass := by
      have hbDens : 1 / 2 + b ≤ dens E G μ ν := by linarith
      dsimp [b, t, q] at *
      nlinarith [hupper, hbias]
    have hbase : b / 2 ≤ b - 2 * gS n := by nlinarith [hbsmall]
    have hmassEq :
        (∑ y ∈ H, ν.w y) = mass := by
      dsimp [mass]
      exact (Finset.sum_ite_mem_eq H ν.w).symm
    rw [hmassEq]
    by_contra hnot
    have hmasslt : mass < b := lt_of_not_ge hnot
    have hqm : q * mass < q * b := mul_lt_mul_of_pos_left hmasslt hqpos
    have hqb : q * b ≤ (1 / 2 : ℝ) * b := mul_le_mul_of_nonneg_right hqle hbpos.le
    linarith
  refine ⟨max 2 (max nlog ngap), ?_⟩
  intro n hn N E X Y hAvail
  have hn2 : 2 ≤ n := le_trans (le_max_left 2 (max nlog ngap)) hn
  have hnmid : max nlog ngap ≤ n := le_trans (le_max_right 2 (max nlog ngap)) hn
  have hnlog' : nlog ≤ n := (le_max_left nlog ngap).trans hnmid
  have hngap' : ngap ≤ n := (le_max_right nlog ngap).trans hnmid
  have hcost : h₀ * Real.log (n : ℝ) ≤ (1 / 1000 : ℝ) * n := hnlog n hnlog'
  have hgapn : 4 ≤ (n : ℝ) ^ ((1 / 100 : ℝ) - h₀) := hngap n hngap'
  have hNposFromLaw {N : ℕ} (μ : Law N) : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hsum : (∑ x : Fin 0, μ.w x) = 0 := by simp
    rw [μ.sum_eq_one] at hsum
    norm_num at hsum
  let Pplus : PairProp := fun n' N' E' μ ν =>
    μ.WidthLE (pw ((1 / 100 : ℚ) : ℝ) n') ∧
    ν.WidthLE (lw ((1 / 100 : ℚ) : ℝ) n') ∧
    (n' : ℝ) ^ (-h₀) ≤ dens E' true μ ν - 1 / 2
  let Pminus : PairProp := fun n' N' E' μ ν =>
    μ.WidthLE (pw ((1 / 100 : ℚ) : ℝ) n') ∧
    ν.WidthLE (lw ((1 / 100 : ℚ) : ℝ) n') ∧
    (n' : ℝ) ^ (-h₀) ≤ dens E' false μ ν - 1 / 2
  have hUnion : AvailableAt κ
      (fun n' N' E' => Pplus.toPatch n' N' E' ∪ Pminus.toPatch n' N' E')
      n N E X Y := by
    intro RX RY hRX hRY
    obtain ⟨A, B, hAB, hA, hB⟩ := hAvail RX RY hRX hRY
    change ∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧
      PBias (pw ((1 / 100 : ℚ) : ℝ)) (lw ((1 / 100 : ℚ) : ℝ)) h₀ n N E μ ν at hAB
    rcases hAB with ⟨μ, ν, hμA, hνB, hprop⟩
    change μ.WidthLE (pw ((1 / 100 : ℚ) : ℝ) n) ∧
      ν.WidthLE (lw ((1 / 100 : ℚ) : ℝ) n) ∧
      (n : ℝ) ^ (-h₀) ≤ |dens E true μ ν - 1 / 2| at hprop
    rcases hprop with ⟨hμwidth, hνwidth, hbias⟩
    have hsign : Pplus n N E μ ν ∨ Pminus n N E μ ν := by
      by_cases hs : 1 / 2 ≤ dens E true μ ν
      · left
        have habs : |dens E true μ ν - 1 / 2| = dens E true μ ν - 1 / 2 :=
          abs_of_nonneg (sub_nonneg.mpr hs)
        have hp : (n : ℝ) ^ (-h₀) ≤ dens E true μ ν - 1 / 2 := by
          rw [← habs]
          exact hbias
        exact ⟨hμwidth, hνwidth, hp⟩
      · right
        have hneg : dens E true μ ν - 1 / 2 < 0 := sub_neg.mpr (lt_of_not_ge hs)
        have habs : |dens E true μ ν - 1 / 2| =
            -(dens E true μ ν - 1 / 2) := abs_of_neg hneg
        have hp : (n : ℝ) ^ (-h₀) ≤ dens E false μ ν - 1 / 2 := by
          have hcomp := dens_add_dens_not E μ ν
          have heq : dens E false μ ν - 1 / 2 =
              -(dens E true μ ν - 1 / 2) := by linarith
          rw [heq, ← habs]
          exact hbias
        exact ⟨hμwidth, hνwidth, hp⟩
    have hmember : (A, B) ∈ Pplus.toPatch n N E ∪ Pminus.toPatch n N E := by
      change (∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧ Pplus n N E μ ν) ∨
        (∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧ Pminus n N E μ ν)
      rcases hsign with hp | hm
      · exact Or.inl ⟨μ, ν, hμA, hνB, hp⟩
      · exact Or.inr ⟨μ, ν, hμA, hνB, hm⟩
    exact ⟨A, B, hmember, hA, hB⟩
  have hsplit := AvailableAt.union hUnion
  have build (G : Colour)
      (hcol : AvailableAt (κ / 2)
        (if G then Pplus.toPatch else Pminus.toPatch) n N E X Y) :
      Nonempty (Menu11 n N E X Y (κ / 2)) := by
    let Q : PairProp := if G then Pplus else Pminus
    have hcolQ : AvailableAt (κ / 2) Q.toPatch n N E X Y := by
      cases G <;> simpa [Q, PairProp.toPatch] using hcol
    let ι : Type := {p : Finset (Fin N) × Finset (Fin N) //
      (p.1.card : ℝ) ≤ (κ / 2) * N ∧ (p.2.card : ℝ) ≤ (κ / 2) * N}
    letI : Fintype ι := Fintype.ofFinite ι
    have hwit (i : ι) : ∃ μ ν : Law N,
        μ.SupportedIn (X \ i.val.1) ∧ ν.SupportedIn (Y \ i.val.2) ∧ Q n N E μ ν := by
      obtain ⟨A, B, hAB, hA, hB⟩ :=
        hcolQ i.val.1 i.val.2 i.property.1 i.property.2
      change ∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧ Q n N E μ ν at hAB
      rcases hAB with ⟨μ, ν, hμA, hνB, hprop⟩
      have hμX : μ.SupportedIn (X \ i.val.1) := by
        intro x hx
        apply hμA
        intro hmem
        exact (hx (hA hmem)).elim
      have hνY : ν.SupportedIn (Y \ i.val.2) := by
        intro y hy
        apply hνB
        intro hmem
        exact (hy (hB hmem)).elim
      exact ⟨μ, ν, hμX, hνY, hprop⟩
    let μraw : ι → Law N := fun i => Classical.choose (hwit i)
    let νraw : ι → Law N := fun i => Classical.choose (Classical.choose_spec (hwit i))
    have hraw (i : ι) :
        (μraw i).SupportedIn (X \ i.val.1) ∧
        (νraw i).SupportedIn (Y \ i.val.2) ∧ Q n N E (μraw i) (νraw i) :=
      Classical.choose_spec (Classical.choose_spec (hwit i))
    have hzeroBudget : (0 : ℝ) ≤ (κ / 2) * (N : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg N)
    have hNposNat : 0 < N := by
      have hEmptyBudget : ((∅ : Finset (Fin N)).card : ℝ) ≤ (κ / 2) * N := by
        simpa using hzeroBudget
      obtain ⟨A, B, hAB, hA, hB⟩ := hcolQ ∅ ∅ hEmptyBudget hEmptyBudget
      change ∃ μ ν : Law N, μ.SupportedIn A ∧ ν.SupportedIn B ∧ Q n N E μ ν at hAB
      rcases hAB with ⟨μ, ν, hμ, hν, hprop⟩
      exact hNposFromLaw μ
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
    let highSet (i : ι) : Finset (Fin N) :=
      Finset.univ.filter fun y => 1 / 2 + 2 * gS n ≤ colDeg E G (μraw i) y
    have hrawFields (i : ι) :
        (μraw i).WidthLE (pw ((1 / 100 : ℚ) : ℝ) n) ∧
        (νraw i).WidthLE (lw ((1 / 100 : ℚ) : ℝ) n) ∧
        (n : ℝ) ^ (-h₀) ≤ dens E G (μraw i) (νraw i) - 1 / 2 := by
      have hp := (hraw i).2.2
      cases G <;> simpa [Q, Pplus, Pminus] using hp
    have hbiasG (i : ι) : (n : ℝ) ^ (-h₀) ≤
        dens E G (μraw i) (νraw i) - 1 / 2 := by
      exact (hrawFields i).2.2
    have hmassLower (i : ι) : (n : ℝ) ^ (-h₀) ≤
        ∑ y ∈ highSet i, (νraw i).w y := by
      exact hheavy_mass E G (μraw i) (νraw i) (hbiasG i) hn2 hcost hgapn
    have hnbpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hbpos : 0 < (n : ℝ) ^ (-h₀) := Real.rpow_pos_of_pos hnbpos _
    have hmasspos (i : ι) : 0 < ∑ y ∈ highSet i, (νraw i).w y :=
      lt_of_lt_of_le hbpos (hmassLower i)
    let νtag (i : ι) : Law N :=
      Law.restrict (νraw i) (highSet i) (hmasspos i)
    have hbInv : ((n : ℝ) ^ (-h₀))⁻¹ = Real.exp (h₀ * Real.log (n : ℝ)) := by
      have hpow : (n : ℝ) ^ (-h₀) = Real.exp (-(h₀ * Real.log (n : ℝ))) := by
        rw [Real.rpow_def_of_pos hnbpos]
        congr 1
        ring
      rw [hpow, Real.exp_neg]
      simp
    have hrawCap (i : ι) (y : Fin N) : (N : ℝ) * (νraw i).w y ≤
        Real.exp ((1 / 100 : ℝ) * n) := by
      have hwidth := (hrawFields i).2.1 y
      have hwidth' : (νraw i).w y ≤ Real.exp ((1 / 100 : ℝ) * n) / N := by
        simpa [lw] using hwidth
      have hmul := (le_div_iff₀ hNpos).mp hwidth'
      nlinarith [hmul]
    have hνwidth (i : ι) : (νtag i).WidthLE ((11 / 1000 : ℝ) * n) := by
      intro y
      by_cases hy : y ∈ highSet i
      · have hscaled : (N : ℝ) * ((νraw i).w y /
            (∑ z ∈ highSet i, (νraw i).w z)) ≤ Real.exp ((11 / 1000 : ℝ) * n) := by
          have hmassInv := (inv_le_inv₀ (hmasspos i) hbpos).2 (hmassLower i)
          calc
            (N : ℝ) * ((νraw i).w y /
                (∑ z ∈ highSet i, (νraw i).w z)) =
                ((N : ℝ) * (νraw i).w y) /
                  (∑ z ∈ highSet i, (νraw i).w z) := by ring
            _ ≤ Real.exp ((1 / 100 : ℝ) * n) /
                (∑ z ∈ highSet i, (νraw i).w z) :=
              div_le_div_of_nonneg_right (hrawCap i y) (hmasspos i).le
            _ = Real.exp ((1 / 100 : ℝ) * n) *
                (∑ z ∈ highSet i, (νraw i).w z)⁻¹ := by rw [div_eq_mul_inv]
            _ ≤ Real.exp ((1 / 100 : ℝ) * n) * ((n : ℝ) ^ (-h₀))⁻¹ :=
              mul_le_mul_of_nonneg_left hmassInv (Real.exp_nonneg _)
            _ = Real.exp ((1 / 100 : ℝ) * n + h₀ * Real.log (n : ℝ)) := by
              rw [hbInv, ← Real.exp_add]
            _ ≤ Real.exp ((11 / 1000 : ℝ) * n) :=
              Real.exp_le_exp.mpr (by nlinarith [hnlog n hnlog'])
        have hscaled' : ((νraw i).w y /
            (∑ z ∈ highSet i, (νraw i).w z)) * (N : ℝ) ≤
              Real.exp ((11 / 1000 : ℝ) * n) := by nlinarith [hscaled]
        have hcap := (le_div_iff₀ hNpos).2 hscaled'
        simpa [νtag, Law.restrict, hy] using hcap
      · simp [νtag, Law.restrict, hy]
        positivity
    have hνSupport (i : ι) : (νtag i).SupportedIn (Y \ i.val.2) := by
      intro y hy
      by_cases hm : y ∈ highSet i
      · have hrawzero := (hraw i).2.1 y hy
        simp [νtag, Law.restrict, hm, hrawzero]
      · simp [νtag, Law.restrict, hm]
    have hμSupport (i : ι) : (μraw i).SupportedIn X := by
      intro x hx
      apply (hraw i).1 x
      intro hmem
      exact hx (Finset.mem_sdiff.mp hmem).1
    have hhigh (i : ι) (y : Fin N) (hy : (νtag i).w y ≠ 0) :
        1 / 2 + 2 * gS n ≤ colDeg E G (μraw i) y := by
      by_contra h
      have hnot : y ∉ highSet i := by
        intro hmem
        exact h (Finset.mem_filter.mp hmem).2
      simp [νtag, Law.restrict, hnot] at hy
    let M : Menu11 n N E X Y (κ / 2) := {
      ι := ι
      G := G
      μ := μraw
      ν := νtag
      μ_supp := hμSupport
      ν_supp := fun i => by
        intro y hy
        exact hνSupport i y (fun hmem => hy (Finset.mem_sdiff.mp hmem).1)
      μ_width := fun i => by simpa [pw] using (hrawFields i).1
      ν_width := hνwidth
      high := hhigh
      avail := by
        intro RX RY hRX hRY
        let i : ι := ⟨(RX, RY), hRX, hRY⟩
        refine ⟨i, ?_, ?_⟩
        · intro x hx
          exact (hraw i).1 x (by
            intro hmem
            exact (Finset.mem_sdiff.mp hmem).2 hx)
        · intro y hy
          exact hνSupport i y (by
            intro hmem
            exact (Finset.mem_sdiff.mp hmem).2 hy)
    }
    exact ⟨M⟩
  rcases hsplit with hp | hm
  · exact build true (by simpa using hp)
  · exact build false (by simpa using hm)

/-- P11.1a(i) (11:52–56, 11:65).  Provisionally draw `Y₀ ∼ ν`, then the `kh` entries `W ∼ ρ_{Y₀}^{⊗kh}`.  Relative
to the reference `μ^{⊗kh}` the marginal density of `W` is `Z_b(W)`, so Lemma 3.7 (`gated_posterior`, first
assertion, `ε = e^{-kh}`) bounds the probability of `Z_b < e^{-kh}` or `Z_b = 0` by `e^{-kh}`.  For the deletion
test of direction `a`, use the posterior of `Y₀` given the other tuples as prior and the reference `μ^{⊗k}` for
the tuple of `a`: its predictive density is `Z_b / Z_{b,-a}`, and Lemma 3.7 with `ε = e^{-.2gk}` bounds the
failure.  The `ν`-average of `testFail` is therefore at most `e^{-kh} + h e^{-.2gk}`, and some `y₀ ∈ supp ν`
attains at most the average.  Every label of `supp ν` has positive degree, so `ρ_{y₀}` is the hit-conditioned
law. -/
theorem base_label {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (hdeg : ∀ y, ν.w y ≠ 0 → 0 < colDeg E G μ y) :
    ∃ y₀, ν.w y₀ ≠ 0 ∧ testFail E G I k g μ ν y₀ ≤
      Real.exp (-((k : ℝ) * Fintype.card I)) + (Fintype.card I : ℝ) * Real.exp (-(1 / 5 : ℝ) * g * k) := by
  classical
  have hstar_sum (y₀ : Fin N) :
      ∑ ws : I → Fin k → Fin N, starW E G μ y₀ ws = 1 := by
    simpa [starW, tupW, tupLaw, FinProb.pi] using
      (FinProb.pi (fun _ : I => tupLaw E G μ y₀ k)).sum_eq_one
  let tupleLik (y : Fin N) (t : Fin k → Fin N) : ℝ :=
    ∏ j, hit E G (t j) y / colDeg E G μ y
  let tupleMu : FinProb (Fin k → Fin N) := FinProb.pi (fun _ : Fin k => μ)
  let ref : FinProb (I → Fin k → Fin N) := FinProb.pi (fun _ : I => tupleMu)
  have htuple (y : Fin N) (hy : ν.w y ≠ 0) (t : Fin k → Fin N) :
      tupleMu.w t * tupleLik y t = (tupLaw E G μ y k).w t := by
    simp only [tupleMu, FinProb.pi, tupleLik, tupLaw, FinProb.pi]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    change μ.w (t j) * (hit E G (t j) y / colDeg E G μ y) =
      (rhoLaw E G μ y).w (t j)
    rw [rhoLaw, dif_pos (hdeg y hy)]
    ring
  have hstar_id (y : Fin N) (hy : ν.w y ≠ 0) (ws : I → Fin k → Fin N) :
      starW E G μ y ws = ref.w ws * lik E G μ ws y := by
    have hrow (a : I) :
        tupW E G μ y (ws a) = tupleMu.w (ws a) * tupleLik y (ws a) := by
      simpa [tupW, tupLaw, tupleLik, FinProb.pi] using (htuple y hy (ws a)).symm
    calc
      starW E G μ y ws = ∏ a, tupleMu.w (ws a) * tupleLik y (ws a) := by
        unfold starW
        apply Finset.prod_congr rfl
        intro a ha
        exact hrow a
      _ = (∏ a, tupleMu.w (ws a)) * ∏ a, tupleLik y (ws a) := by
        rw [Finset.prod_mul_distrib]
      _ = ref.w ws * lik E G μ ws y := by
        simp [ref, FinProb.pi, lik, tupleLik]
  let refDelGiven (a : I) (y : Fin N) : FinProb (I → Fin k → Fin N) :=
    FinProb.pi (fun b : I => if b = a then tupleMu else tupLaw E G μ y k)
  let refDel (a : I) : FinProb (I → Fin k → Fin N) := {
    w := fun ws => ∑ y, ν.w y * (refDelGiven a y).w ws
    nonneg := fun ws => Finset.sum_nonneg fun y hy =>
      mul_nonneg (ν.nonneg y) ((refDelGiven a y).nonneg ws)
    sum_eq_one := by
      calc
        (∑ ws : I → Fin k → Fin N, ∑ y, ν.w y * (refDelGiven a y).w ws) =
            ∑ y, ∑ ws : I → Fin k → Fin N, ν.w y * (refDelGiven a y).w ws := by
          rw [Finset.sum_comm]
        _ = ∑ y, ν.w y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.mul_sum, (refDelGiven a y).sum_eq_one]
          ring
        _ = 1 := ν.sum_eq_one
  }
  have hdel_id (a : I) (y : Fin N) (hy : ν.w y ≠ 0) (ws : I → Fin k → Fin N) :
      ref.w ws * likDel E G μ ws a y =
        (FinProb.pi (fun b : I => if b = a then tupleMu else tupLaw E G μ y k)).w ws := by
    have hq : ref.w ws = ∏ b, tupleMu.w (ws b) := by simp [ref, FinProb.pi]
    have hl : likDel E G μ ws a y = ∏ b ∈ Finset.univ.erase a, tupleLik y (ws b) := by
      simp [likDel, tupleLik]
    have hsplit :
        (∏ b, tupleMu.w (ws b)) = tupleMu.w (ws a) *
          ∏ b ∈ Finset.univ.erase a, tupleMu.w (ws b) :=
      (Finset.mul_prod_erase Finset.univ (fun b => tupleMu.w (ws b)) (Finset.mem_univ a)).symm
    calc
      ref.w ws * likDel E G μ ws a y =
          tupleMu.w (ws a) *
            ((∏ b ∈ Finset.univ.erase a, tupleMu.w (ws b)) *
              ∏ b ∈ Finset.univ.erase a, tupleLik y (ws b)) := by
        rw [hq, hl, hsplit]
        ring
      _ = tupleMu.w (ws a) *
          ∏ b ∈ Finset.univ.erase a, (tupleMu.w (ws b) * tupleLik y (ws b)) := by
        rw [← Finset.prod_mul_distrib]
      _ = tupleMu.w (ws a) *
          ∏ b ∈ Finset.univ.erase a, (tupLaw E G μ y k).w (ws b) := by
        congr 1
        apply Finset.prod_congr rfl
        intro b hb
        exact htuple y hy (ws b)
      _ = (refDelGiven a y).w ws := by
        change tupleMu.w (ws a) *
          ∏ b ∈ Finset.univ.erase a, (tupLaw E G μ y k).w (ws b) =
          ∏ b, (if b = a then tupleMu else tupLaw E G μ y k).w (ws b)
        let f : I → ℝ := fun b => (if b = a then tupleMu else tupLaw E G μ y k).w (ws b)
        have hfa : f a = tupleMu.w (ws a) := by simp [f]
        have hrest : ∏ b ∈ Finset.univ.erase a, f b =
            ∏ b ∈ Finset.univ.erase a, (tupLaw E G μ y k).w (ws b) := by
          apply Finset.prod_congr rfl
          intro b hb
          have hne : b ≠ a := (Finset.mem_erase.mp hb).1
          simp [f, hne]
        have hprod := Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)
        rw [← hprod, hfa, hrest]
  have hrefDel_id (a : I) (ws : I → Fin k → Fin N) :
      (refDel a).w ws = ref.w ws * normZDel E G μ ν ws a := by
    calc
      (refDel a).w ws = ∑ y, ν.w y * (refDelGiven a y).w ws := rfl
      _ = ∑ y, ν.w y * (ref.w ws * likDel E G μ ws a y) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hyν : ν.w y = 0
        · simp [hyν]
        · rw [(hdel_id a y hyν ws).symm]
      _ = ref.w ws * normZDel E G μ ν ws a := by
        rw [normZDel, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
  let mixDensity (ws : I → Fin k → Fin N) : ℝ :=
    ∑ y, ν.w y * starW E G μ y ws
  have hmix_id (ws : I → Fin k → Fin N) :
      mixDensity ws = ref.w ws * normZ E G μ ν ws := by
    calc
      mixDensity ws = ∑ y, ν.w y * (ref.w ws * lik E G μ ws y) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hyν : ν.w y = 0
        · simp [hyν]
        · rw [hstar_id y hyν ws]
      _ = ref.w ws * normZ E G μ ν ws := by
        rw [normZ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
  have hstar_nonneg (y : Fin N) (ws : I → Fin k → Fin N) : 0 ≤ starW E G μ y ws := by
    unfold starW tupW
    apply Finset.prod_nonneg
    intro a ha
    apply Finset.prod_nonneg
    intro j hj
    exact (rhoLaw E G μ y).nonneg (ws a j)
  have hsupp : ∃ y₀, ν.w y₀ ≠ 0 := by
    by_contra h
    push_neg at h
    have hs : ∑ y, ν.w y = 0 := by simp [h]
    rw [ν.sum_eq_one] at hs
    norm_num at hs
  obtain ⟨y₀, hy₀⟩ := hsupp
  let eps0 : ℝ := Real.exp (-((k : ℝ) * Fintype.card I))
  let epsA : ℝ := Real.exp (-(1 / 5 : ℝ) * g * k)
  let bad0 (ws : I → Fin k → Fin N) : Prop :=
    mixDensity ws < eps0 * ref.w ws ∨ mixDensity ws = 0
  let badA (a : I) (ws : I → Fin k → Fin N) : Prop :=
    mixDensity ws < epsA * (refDel a).w ws ∨ mixDensity ws = 0
  have hF0 : ∀ y ws, 0 ≤ starW E G μ y ws := hstar_nonneg
  have heps0 : 0 < eps0 := Real.exp_pos _
  have hepsA : 0 < epsA := Real.exp_pos _
  have hmix_nonneg (ws : I → Fin k → Fin N) : 0 ≤ mixDensity ws := by
    unfold mixDensity
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (ν.nonneg y) (hstar_nonneg y ws)
  have hgp0 :
      (∑ ws : I → Fin k → Fin N, if bad0 ws then mixDensity ws else 0) ≤ eps0 := by
    simpa [bad0, mixDensity, eps0] using
      (HypercubeRamsey.gated_posterior ν (fun y ws => starW E G μ y ws) hF0 ref eps0 0 heps0).1
  have hgpA (a : I) :
      (∑ ws : I → Fin k → Fin N, if badA a ws then mixDensity ws else 0) ≤ epsA := by
    simpa [badA, mixDensity, epsA] using
      (HypercubeRamsey.gated_posterior ν (fun y ws => starW E G μ y ws) hF0
        (refDel a) epsA 0 hepsA).1
  have hpoint (ws : I → Fin k → Fin N) :
      mixDensity ws * (if Passes E G g μ ν ws then 0 else 1) ≤
        (if bad0 ws then mixDensity ws else 0) +
          ∑ a : I, if badA a ws then mixDensity ws else 0 := by
    by_cases hpass : Passes E G g μ ν ws
    · simp [hpass]
      apply add_nonneg
      · split_ifs <;> [exact hmix_nonneg ws; exact le_rfl]
      · apply Finset.sum_nonneg
        intro a ha
        split_ifs <;> [exact hmix_nonneg ws; exact le_rfl]
    · by_cases hbad0 : bad0 ws
      · have hsum_nonneg : 0 ≤ ∑ a : I, if badA a ws then mixDensity ws else 0 := by
          apply Finset.sum_nonneg
          intro a ha
          split_ifs <;> [exact hmix_nonneg ws; exact le_rfl]
        simp [hpass, hbad0]
        exact hsum_nonneg
      · have hqpos : 0 < ref.w ws := by
          by_contra hq
          have hq0 : ref.w ws = 0 := le_antisymm (le_of_not_gt hq) (ref.nonneg ws)
          apply hbad0
          right
          rw [hmix_id, hq0]
          ring
        have hnorm : eps0 ≤ normZ E G μ ν ws := by
          by_contra hlt
          have hlt' : normZ E G μ ν ws < eps0 := lt_of_not_ge hlt
          apply hbad0
          left
          rw [hmix_id]
          nlinarith [mul_lt_mul_of_pos_left hlt' hqpos]
        have hnormpos : 0 < normZ E G μ ν ws := lt_of_lt_of_le heps0 hnorm
        have hnotall : ¬ ∀ a, epsA * normZDel E G μ ν ws a ≤ normZ E G μ ν ws := by
          intro hall
          exact hpass ⟨hnormpos, hnorm, hall⟩
        push Not at hnotall
        obtain ⟨a, hratio⟩ := hnotall
        have hbad : badA a ws := by
          left
          rw [hmix_id, hrefDel_id]
          have hstrict := mul_lt_mul_of_pos_left hratio hqpos
          dsimp [epsA]
          nlinarith
        have hsum : mixDensity ws ≤ ∑ a : I, if badA a ws then mixDensity ws else 0 := by
          have hsingle := Finset.single_le_sum
            (s := Finset.univ)
            (f := fun b : I => if badA b ws then mixDensity ws else 0)
            (fun b hb => by
              by_cases hbadb : badA b ws
              · simp [hbadb, hmix_nonneg ws]
              · simp [hbadb])
            (Finset.mem_univ a)
          simpa [hbad] using hsingle
        simpa [hpass, hbad0, hbad] using hsum
  have havg_eq :
      (∑ y, ν.w y * testFail E G I k g μ ν y) =
        ∑ ws : I → Fin k → Fin N,
          mixDensity ws * (if Passes E G g μ ν ws then 0 else 1) := by
    simp only [testFail]
    calc
      (∑ y, ν.w y * ∑ ws : I → Fin k → Fin N,
          starW E G μ y ws * (if Passes E G g μ ν ws then 0 else 1)) =
          ∑ y, ∑ ws : I → Fin k → Fin N, ν.w y *
            (starW E G μ y ws * (if Passes E G g μ ν ws then 0 else 1)) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact Finset.mul_sum Finset.univ
          (fun ws => starW E G μ y ws * (if Passes E G g μ ν ws then 0 else 1)) (ν.w y)
      _ = ∑ ws : I → Fin k → Fin N, ∑ y, ν.w y *
          (starW E G μ y ws * (if Passes E G g μ ν ws then 0 else 1)) := by
        rw [Finset.sum_comm]
      _ = ∑ ws : I → Fin k → Fin N,
          mixDensity ws * (if Passes E G g μ ν ws then 0 else 1) := by
        apply Finset.sum_congr rfl
        intro ws hws
        calc
          (∑ y, ν.w y * (starW E G μ y ws * (if Passes E G g μ ν ws then 0 else 1))) =
              (if Passes E G g μ ν ws then 0 else 1) *
                ∑ y, ν.w y * starW E G μ y ws := by
            calc
              (∑ y, ν.w y * (starW E G μ y ws * (if Passes E G g μ ν ws then 0 else 1))) =
                  ∑ y, (if Passes E G g μ ν ws then 0 else 1) *
                    (ν.w y * starW E G μ y ws) := by
                apply Finset.sum_congr rfl
                intro y hy
                ring
              _ = _ := (Finset.mul_sum Finset.univ
                (fun y => ν.w y * starW E G μ y ws)
                (if Passes E G g μ ν ws then 0 else 1)).symm
          _ = mixDensity ws * (if Passes E G g μ ν ws then 0 else 1) := by
            simp [mixDensity]
  have havg :
      (∑ y, ν.w y * testFail E G I k g μ ν y) ≤
        eps0 + (Fintype.card I : ℝ) * epsA := by
    calc
      (∑ y, ν.w y * testFail E G I k g μ ν y) =
          ∑ ws : I → Fin k → Fin N,
            mixDensity ws * (if Passes E G g μ ν ws then 0 else 1) := havg_eq
      _ ≤ ∑ ws : I → Fin k → Fin N,
            ((if bad0 ws then mixDensity ws else 0) +
              ∑ a : I, if badA a ws then mixDensity ws else 0) := by
        apply Finset.sum_le_sum
        intro ws hws
        exact hpoint ws
      _ = (∑ ws : I → Fin k → Fin N, if bad0 ws then mixDensity ws else 0) +
            ∑ a : I, ∑ ws : I → Fin k → Fin N,
              if badA a ws then mixDensity ws else 0 := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ ≤ eps0 + (Fintype.card I : ℝ) * epsA := by
        have hsumA :
            (∑ a : I, ∑ ws : I → Fin k → Fin N,
              if badA a ws then mixDensity ws else 0) ≤
              (Fintype.card I : ℝ) * epsA := by
          calc
            _ ≤ ∑ a : I, epsA := Finset.sum_le_sum fun a ha => hgpA a
            _ = (Fintype.card I : ℝ) * epsA := by simp [Finset.sum_const, nsmul_eq_mul]
        exact add_le_add hgp0 hsumA
  let B : ℝ := eps0 + (Fintype.card I : ℝ) * epsA
  have hresult : ∃ y₀, ν.w y₀ ≠ 0 ∧ testFail E G I k g μ ν y₀ ≤ B := by
    by_contra hgood
    have hbad : ∀ y, ν.w y ≠ 0 → B < testFail E G I k g μ ν y := by
      intro y hy
      by_contra hle
      exact hgood ⟨y, hy, le_of_not_gt hle⟩
    have hstrict :
        (∑ y, B * ν.w y) < ∑ y, ν.w y * testFail E G I k g μ ν y := by
      apply Finset.sum_lt_sum
      · intro y hy
        by_cases hν : ν.w y = 0
        · simp [hν]
        · have hνpos : 0 < ν.w y := lt_of_le_of_ne (ν.nonneg y) (Ne.symm hν)
          have hterm := mul_le_mul_of_nonneg_left (le_of_lt (hbad y hν)) (ν.nonneg y)
          simpa [mul_comm] using hterm
      · exact ⟨y₀, Finset.mem_univ y₀, by
          have hνpos : 0 < ν.w y₀ := lt_of_le_of_ne (ν.nonneg y₀) (Ne.symm hy₀)
          have hterm := mul_lt_mul_of_pos_left (hbad y₀ hy₀) hνpos
          simpa [mul_comm] using hterm⟩
    have hleft : ∑ y, B * ν.w y = B := by rw [← Finset.mul_sum, ν.sum_eq_one, mul_one]
    rw [hleft] at hstrict
    linarith [havg]
  obtain ⟨yBase, hyBase, htest⟩ := hresult
  refine ⟨yBase, hyBase, ?_⟩
  simpa [B, eps0, epsA] using htest

/-- The row facts of P11.1a(ii) and of the mean odd row `π_i` (11:57–63, 11:100). -/
structure RowFacts {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (y₀ : Fin N) (L : ℝ) : Prop where
  row_nonneg : ∀ (ws : I → Fin k → Fin N) y, 0 ≤ oddRowW E G g μ ν ws y
  row_sum : ∀ ws : I → Fin k → Fin N, ∑ y, oddRowW E G g μ ν ws y = 1
  row_supp : ∀ (ws : I → Fin k → Fin N) y, oddRowW E G g μ ν ws y ≠ 0 → ν.w y ≠ 0
  row_cap : ∀ (ws : I → Fin k → Fin N) y, (N : ℝ) * oddRowW E G g μ ν ws y ≤ L
  pi_nonneg : ∀ y, 0 ≤ meanOddRow E G I k g μ ν y₀ y
  pi_sum : ∑ y, meanOddRow E G I k g μ ν y₀ y = 1
  pi_supp : ∀ y, meanOddRow E G I k g μ ν y₀ y ≠ 0 → ν.w y ≠ 0
  pi_cap : ∀ y, (N : ℝ) * meanOddRow E G I k g μ ν y₀ y ≤ L

/-- P11.1a(ii) (11:57–63, 11:100).  A passing row is `ν L_b / Z_b` with `Z_b ≥ e^{-kh} > 0`, `N ν ≤ e^{.011n}` and
`L_b ≤ (1/2 + 2g)^{-kh}` on `supp ν`, so `log(N max p_b^W) ≤ .011n + kh(1 - log(1/2 + 2g)) ≤ .02n` as
`kh = O(n^{.3})`; the fallback row is `ν`.  The tuple weights at `y₀ ∈ supp ν` sum to one (`d_G(μ, y₀) > 0`), so
`π_i` is an average of rows. -/
theorem odd_row_facts :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (μ ν : Law N) (y₀ : Fin N),
      ν.WidthLE ((11 / 1000 : ℝ) * n) → (∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * gS n ≤ colDeg E G μ y) →
      ν.w y₀ ≠ 0 →
      RowFacts E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ (Real.exp ((n : ℝ) / 50)) := by
  classical
  have hpow : ∀ᶠ n : ℕ in atTop, (500 : ℝ) ≤ (n : ℝ) ^ ((7 : ℝ) / 10) := by
    have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ((7 : ℝ) / 10)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (7 : ℝ) / 10)).comp
        tendsto_natCast_atTop_atTop
    exact htend.eventually_ge_atTop 500
  have hsmall : ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ ((3 : ℝ) / 10) ≤ (9 / 1000 : ℝ) * n := by
    filter_upwards [hpow, (eventually_ge_atTop 1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n)] with n hn hn1
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmul : (n : ℝ) ^ ((3 : ℝ) / 10) * (n : ℝ) ^ ((7 : ℝ) / 10) = n := by
      rw [← Real.rpow_add hnreal]
      rw [show (3 : ℝ) / 10 + (7 : ℝ) / 10 = 1 by norm_num, Real.rpow_one]
    have hcoef : 4 ≤ (9 / 1000 : ℝ) * (n : ℝ) ^ ((7 : ℝ) / 10) := by
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hcoef
      (Real.rpow_nonneg hnreal.le ((3 : ℝ) / 10))
    nlinarith [hscaled, hmul]
  obtain ⟨nSmall, hnSmall⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max 1 nSmall, ?_⟩
  intro n hn N E G μ ν y₀ hνwidth hhigh hy₀
  have hn1 : 1 ≤ n := le_trans (le_max_left 1 nSmall) hn
  have hnSmall' : nSmall ≤ n := le_trans (le_max_right 1 nSmall) hn
  have hnreal1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnreal0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hIcard : (Fintype.card (InnerCoord n) : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 10) := by
    have hinj : Function.Injective
        (fun j : InnerCoord n => (⟨j.val, j.property⟩ : Fin (hIn n))) := by
      intro j j' h
      have hv : j.val.val = j'.val.val := congrArg (fun x : Fin (hIn n) => x.val) h
      apply Subtype.ext
      exact Fin.ext hv
    have hcard : Fintype.card (InnerCoord n) ≤ hIn n :=
      by simpa using (Fintype.card_le_of_injective _ hinj)
    calc
      (Fintype.card (InnerCoord n) : ℝ) ≤ (hIn n : ℝ) := by exact_mod_cast hcard
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 10) := by
        unfold hIn
        exact Nat.floor_le (by positivity)
  have hkbound : (kTup n : ℝ) ≤
      (n : ℝ) ^ ((1 : ℝ) / 5) + 1 := by
    unfold kTup
    exact (Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith [hnreal1]) _)).le
  have hexponent : (n : ℝ) ^ ((1 : ℝ) / 10) ≤
      (n : ℝ) ^ ((3 : ℝ) / 10) :=
    Real.rpow_le_rpow_of_exponent_le hnreal1 (by norm_num)
  have hkh : (2 : ℝ) * (kTup n : ℝ) * Fintype.card (InnerCoord n) ≤
      (9 / 1000 : ℝ) * n := by
    have hprod : (kTup n : ℝ) * Fintype.card (InnerCoord n) ≤
        2 * (n : ℝ) ^ ((3 : ℝ) / 10) := by
      calc
        (kTup n : ℝ) * Fintype.card (InnerCoord n) ≤
            ((n : ℝ) ^ ((1 : ℝ) / 5) + 1) *
              (n : ℝ) ^ ((1 : ℝ) / 10) := by
          exact mul_le_mul hkbound hIcard (by positivity) (by positivity)
        _ = (n : ℝ) ^ ((3 : ℝ) / 10) + (n : ℝ) ^ ((1 : ℝ) / 10) := by
          rw [add_mul, ← Real.rpow_add hnreal0]
          congr 1 <;> ring
        _ ≤ 2 * (n : ℝ) ^ ((3 : ℝ) / 10) := by nlinarith [hexponent]
    have hsmalln := hnSmall n hnSmall'
    nlinarith
  have hNposNat : 0 < N := by
    by_contra hN
    have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    have hsum : (∑ _y : Fin 0, ν.w _y) = 0 := by simp
    rw [ν.sum_eq_one] at hsum
    norm_num at hsum
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNposNat
  have hgh : 0 ≤ gS n := by unfold gS; positivity
  have hdegree_nonneg (y : Fin N) : 0 ≤ colDeg E G μ y := by
    unfold colDeg
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg (μ.nonneg x)
    split_ifs <;> norm_num
  have hlik_nonneg (ws : InnerCoord n → Fin (kTup n) → Fin N) (y : Fin N) :
      0 ≤ lik E G μ ws y := by
    unfold lik
    apply Finset.prod_nonneg
    intro a ha
    apply Finset.prod_nonneg
    intro j hj
    exact div_nonneg (by
      unfold hit
      split_ifs <;> norm_num) (hdegree_nonneg y)
  have hcapNu (y : Fin N) : (N : ℝ) * ν.w y ≤
      Real.exp ((11 / 1000 : ℝ) * n) := by
    have hw := hνwidth y
    have hmul := (le_div_iff₀ hNpos).mp hw
    nlinarith [hmul]
  have hlik_bound (ws : InnerCoord n → Fin (kTup n) → Fin N) (y : Fin N)
      (hy : ν.w y ≠ 0) :
      lik E G μ ws y ≤ Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) := by
    have hd : 1 / 2 ≤ colDeg E G μ y := by
      exact le_trans (by linarith [hgh]) (hhigh y hy)
    have hdpos : 0 < colDeg E G μ y := lt_of_lt_of_le (by norm_num) hd
    have hfactor (a : InnerCoord n) (j : Fin (kTup n)) :
        hit E G (ws a j) y / colDeg E G μ y ≤ Real.exp 1 := by
      have hhit : hit E G (ws a j) y ≤ 1 := by
        unfold hit
        split_ifs <;> norm_num
      have hdiv : hit E G (ws a j) y / colDeg E G μ y ≤ 2 := by
        apply (div_le_iff₀ hdpos).2
        nlinarith [hhit]
      have hexp : 2 ≤ Real.exp 1 := by
        have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
        norm_num at h ⊢
        linarith
      exact hdiv.trans hexp
    unfold lik
    calc
      (∏ a, ∏ j, hit E G (ws a j) y / colDeg E G μ y) ≤
          ∏ a, ∏ j : Fin (kTup n), Real.exp 1 := by
        apply Finset.prod_le_prod₀
        · intro a ha
          apply Finset.prod_nonneg
          intro j hj
          exact div_nonneg (by
            unfold hit
            split_ifs <;> norm_num) (hdegree_nonneg y)
        · intro a ha
          apply Finset.prod_le_prod₀
          · intro j hj
            exact div_nonneg (by
              unfold hit
              split_ifs <;> norm_num) (hdegree_nonneg y)
          · intro j hj
            exact hfactor a j
      _ = Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) := by
        simp_rw [← Real.exp_sum]
        congr 1
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hZinv (ws : InnerCoord n → Fin (kTup n) → Fin N)
      (hp : Passes E G (gS n) μ ν ws) :
      (normZ E G μ ν ws)⁻¹ ≤
        Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) := by
    have hZpos := hp.1
    have hZlow := hp.2.1
    have hinv : (1 : ℝ) / normZ E G μ ν ws ≤
        Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) := by
      apply (div_le_iff₀ hZpos).2
      calc
        1 = Real.exp (-((kTup n : ℝ) * Fintype.card (InnerCoord n))) *
            Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) := by
          rw [← Real.exp_add]
          simp
        _ ≤ normZ E G μ ν ws *
            Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) :=
          mul_le_mul_of_nonneg_right hZlow (Real.exp_nonneg _)
        _ = Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) *
            normZ E G μ ν ws := by ring
    simpa [one_div] using hinv
  have hrow_nonneg (ws : InnerCoord n → Fin (kTup n) → Fin N) (y : Fin N) :
      0 ≤ oddRowW E G (gS n) μ ν ws y := by
    unfold oddRowW
    split_ifs with hp
    · exact div_nonneg (mul_nonneg (ν.nonneg y) (hlik_nonneg ws y)) hp.1.le
    · exact ν.nonneg y
  have hrow_sum (ws : InnerCoord n → Fin (kTup n) → Fin N) :
      ∑ y, oddRowW E G (gS n) μ ν ws y = 1 := by
    by_cases hp : Passes E G (gS n) μ ν ws
    · simp only [oddRowW, if_pos hp]
      rw [← Finset.sum_div]
      change normZ E G μ ν ws / normZ E G μ ν ws = 1
      exact div_self hp.1.ne'
    · simp [oddRowW, hp, ν.sum_eq_one]
  have hrow_supp (ws : InnerCoord n → Fin (kTup n) → Fin N) (y : Fin N)
      (hy : oddRowW E G (gS n) μ ν ws y ≠ 0) : ν.w y ≠ 0 := by
    by_contra hν
    simp [oddRowW, hν] at hy
  have hrow_cap (ws : InnerCoord n → Fin (kTup n) → Fin N) (y : Fin N) :
      (N : ℝ) * oddRowW E G (gS n) μ ν ws y ≤ Real.exp ((n : ℝ) / 50) := by
    by_cases hy : ν.w y = 0
    · simp [oddRowW, hy]
      exact le_trans (by positivity : 0 ≤ Real.exp ((11 / 1000 : ℝ) * n))
        (Real.exp_le_exp.mpr (by nlinarith))
    · have hdegree := hhigh y hy
      by_cases hp : Passes E G (gS n) μ ν ws
      · have hprod :
            (N : ℝ) * (ν.w y * lik E G μ ws y / normZ E G μ ν ws) ≤
              Real.exp ((11 / 1000 : ℝ) * n +
                2 * ((kTup n : ℝ) * Fintype.card (InnerCoord n))) := by
          calc
            (N : ℝ) * (ν.w y * lik E G μ ws y / normZ E G μ ν ws) =
                ((N : ℝ) * ν.w y) * lik E G μ ws y * (normZ E G μ ν ws)⁻¹ := by ring
            _ ≤ Real.exp ((11 / 1000 : ℝ) * n) *
                Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) *
                Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) := by
              have hlik := hlik_bound ws y hy
              have hinv := hZinv ws hp
              have hA := hcapNu y
              have hAn : 0 ≤ (N : ℝ) * ν.w y := mul_nonneg (Nat.cast_nonneg N) (ν.nonneg y)
              have hBn : 0 ≤ lik E G μ ws y := hlik_nonneg ws y
              have hCn : 0 ≤ (normZ E G μ ν ws)⁻¹ := inv_nonneg.mpr hp.1.le
              calc
                ((N : ℝ) * ν.w y * lik E G μ ws y) * (normZ E G μ ν ws)⁻¹ ≤
                    (Real.exp ((11 / 1000 : ℝ) * n) * lik E G μ ws y) *
                      (normZ E G μ ν ws)⁻¹ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hA hBn) hCn
                _ ≤ (Real.exp ((11 / 1000 : ℝ) * n) *
                      Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n))) *
                      (normZ E G μ ν ws)⁻¹ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hlik (Real.exp_nonneg _)) hCn
                _ ≤ (Real.exp ((11 / 1000 : ℝ) * n) *
                      Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n))) *
                      Real.exp ((kTup n : ℝ) * Fintype.card (InnerCoord n)) :=
                  mul_le_mul_of_nonneg_left hinv
                    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
            _ = Real.exp ((11 / 1000 : ℝ) * n +
                2 * ((kTup n : ℝ) * Fintype.card (InnerCoord n))) := by
              rw [← Real.exp_add]
              rw [← Real.exp_add]
              congr 1
              ring
        have hfinal :
            (11 / 1000 : ℝ) * n + 2 * ((kTup n : ℝ) * Fintype.card (InnerCoord n)) ≤
              (1 / 50 : ℝ) * n := by nlinarith [hkh]
        have hcap := hprod.trans (Real.exp_le_exp.mpr hfinal)
        have hcap' : (N : ℝ) * oddRowW E G (gS n) μ ν ws y ≤
            Real.exp ((1 / 50 : ℝ) * n) := by simpa [oddRowW, hp] using hcap
        convert hcap' using 1 <;> congr 1 <;> ring
      · have hwidth := hcapNu y
        have hfinal : (11 / 1000 : ℝ) * n ≤ (1 / 50 : ℝ) * n := by nlinarith
        have hcap := hwidth.trans (Real.exp_le_exp.mpr hfinal)
        have hcap' : (N : ℝ) * oddRowW E G (gS n) μ ν ws y ≤
            Real.exp ((1 / 50 : ℝ) * n) := by simpa [oddRowW, hp] using hcap
        convert hcap' using 1 <;> congr 1 <;> ring
  have hstar_nonneg (ws : InnerCoord n → Fin (kTup n) → Fin N) :
      0 ≤ starW E G μ y₀ ws := by
    unfold starW tupW
    apply Finset.prod_nonneg
    intro a ha
    apply Finset.prod_nonneg
    intro j hj
    exact (rhoLaw E G μ y₀).nonneg (ws a j)
  have hstar_sum :
      ∑ ws : InnerCoord n → Fin (kTup n) → Fin N, starW E G μ y₀ ws = 1 := by
    simpa [starW, tupW, tupLaw, FinProb.pi] using
      (FinProb.pi (fun _ : InnerCoord n => tupLaw E G μ y₀ (kTup n))).sum_eq_one
  have hmean_nonneg (y : Fin N) :
      0 ≤ meanOddRow E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ y := by
    unfold meanOddRow
    apply Finset.sum_nonneg
    intro ws hws
    exact mul_nonneg (hstar_nonneg ws) (hrow_nonneg ws y)
  have hmean_sum :
      ∑ y, meanOddRow E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ y = 1 := by
    unfold meanOddRow
    calc
      (∑ y, ∑ ws : InnerCoord n → Fin (kTup n) → Fin N,
        starW E G μ y₀ ws * oddRowW E G (gS n) μ ν ws y) =
          ∑ ws : InnerCoord n → Fin (kTup n) → Fin N,
            starW E G μ y₀ ws * ∑ y, oddRowW E G (gS n) μ ν ws y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ws hws
        rw [← Finset.mul_sum]
      _ = ∑ ws : InnerCoord n → Fin (kTup n) → Fin N, starW E G μ y₀ ws := by
        apply Finset.sum_congr rfl
        intro ws hws
        rw [hrow_sum ws, mul_one]
      _ = 1 := hstar_sum
  have hmean_supp (y : Fin N)
      (hy : meanOddRow E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ y ≠ 0) :
      ν.w y ≠ 0 := by
    by_contra hν
    have hzero : ∀ ws : InnerCoord n → Fin (kTup n) → Fin N,
        oddRowW E G (gS n) μ ν ws y = 0 := by
      intro ws
      simp [oddRowW, hν]
    simp [meanOddRow, hzero] at hy
  have hmean_cap (y : Fin N) :
      (N : ℝ) * meanOddRow E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ y ≤
        Real.exp ((n : ℝ) / 50) := by
    unfold meanOddRow
    calc
      (N : ℝ) * ∑ ws : InnerCoord n → Fin (kTup n) → Fin N,
          starW E G μ y₀ ws * oddRowW E G (gS n) μ ν ws y =
          ∑ ws, starW E G μ y₀ ws * ((N : ℝ) * oddRowW E G (gS n) μ ν ws y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ws hws
        ring
      _ ≤ ∑ ws, starW E G μ y₀ ws * Real.exp ((n : ℝ) / 50) := by
        apply Finset.sum_le_sum
        intro ws hws
        exact mul_le_mul_of_nonneg_left (hrow_cap ws y) (hstar_nonneg ws)
      _ = Real.exp ((n : ℝ) / 50) := by
        rw [← Finset.sum_mul, hstar_sum, one_mul]
  exact {
    row_nonneg := hrow_nonneg
    row_sum := hrow_sum
    row_supp := hrow_supp
    row_cap := hrow_cap
    pi_nonneg := hmean_nonneg
    pi_sum := hmean_sum
    pi_supp := hmean_supp
    pi_cap := hmean_cap }

/-- P11.1b (11:66–90).  Fix the radius-two data except the centre tuple `w` (prior `ρ_{y₀}^{⊗k}`).  For internal
outputs `t`, `F_w(t)` is the product of the `h` neighbouring rows times the indicator that their tests pass;
each passing row is at most `(1/2 + 2g)^{-k} e^{.2gk}` times its deletion row, so `F_w(t) ≤ e^{(log 2-2g)kh} Q(t)`
with `Q` the product of the deletion rows (fixed fallbacks at zero denominators).  Lemma 3.7 bounds the event
`m = 0` or `m < e^{-.5gkh} Q` by `e^{-.5gkh}`.  Outside it the posterior of `w` has atoms at most
`N^{-k} e^{(log 2 - 1.5g)kh + k n^{.01} + O(k)} ≤ N^{-k} e^{(log 2 - g)kh}` (`width μ ≤ n^.01 = o(gh)`) and is
supported on tuples of common neighbours, so the common-neighbour set has at least `N e^{-(log 2 - g)h}` labels,
above the cutoff.  Each of the `h` neighbouring rows fails its tests with probability `testFail` (its `h` tuples
are independent `ρ_{y₀}^{⊗k}` draws). -/
theorem sigma_fail :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (μ ν : Law N) (y₀ : Fin N),
      μ.WidthLE ((n : ℝ) ^ ((1 : ℝ) / 100)) → (∀ y, ν.w y ≠ 0 → 1 / 2 + 2 * gS n ≤ colDeg E G μ y) →
      ν.w y₀ ≠ 0 →
      sigmaFail E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ ≤
        Real.exp (-(1 / 2 : ℝ) * gS n * kTup n * Fintype.card (InnerCoord n)) +
          (Fintype.card (InnerCoord n) : ℝ) * testFail E G (InnerCoord n) (kTup n) (gS n) μ ν y₀ := by
  exact HypercubeRamsey.Lane_q_s11_slice.sigma_fail_q_s11_slice

/-- The facts of the mean even row `α_i` (11:100). -/
structure AlphaFacts {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (y₀ : Fin N) : Prop where
  nonneg : ∀ x, 0 ≤ meanEvenRow E G I k g μ ν y₀ x
  sum_le : ∑ x, meanEvenRow E G I k g μ ν y₀ x ≤ 1
  supp : ∀ x, meanEvenRow E G I k g μ ν y₀ x ≠ 0 → μ.w x ≠ 0

/-- `α_i` is a subprobability on `supp μ_i` (11:100): `σ_v` has mass zero or one on the common-neighbour set
inside `supp μ_i`, and the tuple and output weights are probabilities. -/
theorem alpha_facts {N : ℕ} (E : Fin N → Fin N → Prop) (G : Colour) (I : Type) [Fintype I] [DecidableEq I]
    (k : ℕ) (g : ℝ) (μ ν : Law N) (y₀ : Fin N)
    (hrow0 : ∀ (ws : I → Fin k → Fin N) y, 0 ≤ oddRowW E G g μ ν ws y)
    (hrow1 : ∀ ws : I → Fin k → Fin N, ∑ y, oddRowW E G g μ ν ws y = 1) :
    AlphaFacts E G I k g μ ν y₀ := by
  classical
  have hrow : ∀ ws : I → Fin k → Fin N, ∀ y, 0 ≤ oddRowW E G g μ ν ws y := hrow0
  have hσ_nonneg (z : I → Fin N) (x : Fin N) : 0 ≤ sigmaW E G g μ z x := by
    unfold sigmaW
    split_ifs with h
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  have hσ_sum (z : I → Fin N) : ∑ x, sigmaW E G g μ z x ≤ 1 := by
    let S := commonSet E G μ z
    by_cases hc : (N : ℝ) * Real.exp (-((Real.log 2 - g / 2) * Fintype.card I)) ≤ (S.card : ℝ)
    · by_cases hS : S.card = 0
      · have hzero : (S.card : ℝ)⁻¹ = 0 := by simp [hS]
        norm_num [sigmaW, S, hc, hS, hzero]
      · have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS
        have hmass : (∑ x, sigmaW E G g μ z x) = 1 := by
          calc
            (∑ x, sigmaW E G g μ z x) = (S.card : ℝ) * (S.card : ℝ)⁻¹ := by
              simp [sigmaW, S, hc, Finset.sum_ite_mem, Finset.univ_inter,
                Finset.sum_const, nsmul_eq_mul]
            _ = 1 := mul_inv_cancel₀ hcard
        rw [hmass]
    · simp [sigmaW, S, hc]
  have hrowSum (ws : I → Fin k → Fin N) : ∑ y, oddRowW E G g μ ν ws y = 1 := hrow1 ws
  let row (W : Option (Pair I) → Fin k → Fin N) : I → FinProb (Fin N) := fun a =>
    ⟨oddRowW E G g μ ν (ballStar W a), hrow0 (ballStar W a),
      hrowSum (ballStar W a)⟩
  have hout_sum (W : Option (Pair I) → Fin k → Fin N) :
      ∑ z : I → Fin N, outW E G g μ ν W z = 1 := by
    simpa [outW, row, FinProb.pi] using (FinProb.pi (row W)).sum_eq_one
  have hout_nonneg (W : Option (Pair I) → Fin k → Fin N) (z : I → Fin N) :
      0 ≤ outW E G g μ ν W z := by
    unfold outW
    exact Finset.prod_nonneg fun a _ => hrow0 (ballStar W a) (z a)
  have hball_nonneg (W : Option (Pair I) → Fin k → Fin N) :
      0 ≤ ballW E G μ y₀ W := by
    unfold ballW tupW
    apply Finset.prod_nonneg
    intro o ho
    apply Finset.prod_nonneg
    intro j hj
    exact (rhoLaw E G μ y₀).nonneg (W o j)
  have hball_sum :
      ∑ W : Option (Pair I) → Fin k → Fin N, ballW E G μ y₀ W = 1 := by
    simpa [ballW, tupW, tupLaw, FinProb.pi] using
      (FinProb.pi (fun _ : Option (Pair I) => tupLaw E G μ y₀ k)).sum_eq_one
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold meanEvenRow
    apply Finset.sum_nonneg
    intro W hW
    apply mul_nonneg (hball_nonneg W)
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hout_nonneg W z) (hσ_nonneg z x)
  · calc
      (∑ x, meanEvenRow E G I k g μ ν y₀ x) =
          ∑ W : Option (Pair I) → Fin k → Fin N,
            ballW E G μ y₀ W *
              ∑ z : I → Fin N, outW E G g μ ν W z * ∑ x, sigmaW E G g μ z x := by
        simp only [meanEvenRow]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro W hW
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro z hz
        rw [← Finset.mul_sum]
      _ ≤ ∑ W : Option (Pair I) → Fin k → Fin N, ballW E G μ y₀ W * 1 := by
        apply Finset.sum_le_sum
        intro W hW
        apply mul_le_mul_of_nonneg_left _ (hball_nonneg W)
        calc
          (∑ z : I → Fin N, outW E G g μ ν W z * ∑ x, sigmaW E G g μ z x) ≤
              ∑ z : I → Fin N, outW E G g μ ν W z * 1 := by
            apply Finset.sum_le_sum
            intro z hz
            exact mul_le_mul_of_nonneg_left (hσ_sum z) (hout_nonneg W z)
          _ = 1 := by simpa using hout_sum W
      _ = 1 := by simpa using hball_sum
  · intro x hx
    by_contra hμ
    have hsigma : ∀ z : I → Fin N, sigmaW E G g μ z x = 0 := by
      intro z
      unfold sigmaW commonSet
      split_ifs with h
      · rcases h with ⟨hmem, _⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact (hmem.1 hμ).elim
      · rfl
    simp only [meanEvenRow, hsigma, mul_zero, Finset.sum_const_zero] at hx
    exact hx rfl

/-- All slice facts of a menu with base labels (P11.1a, P11.1b). -/
structure SliceFacts {n N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
    (M : Menu11 n N E X Y κ) (y₀ : M.ι → Fin N) : Prop where
  base : ∀ i, (M.ν i).w (y₀ i) ≠ 0
  test : ∀ i, testFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) ≤
    Real.exp (-((kTup n : ℝ) * Fintype.card (InnerCoord n))) +
      (Fintype.card (InnerCoord n) : ℝ) * Real.exp (-(1 / 5 : ℝ) * gS n * kTup n)
  rows : ∀ i, RowFacts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) (Real.exp ((n : ℝ) / 50))
  sigma : ∀ i, sigmaFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i) ≤
    Real.exp (-(1 / 2 : ℝ) * gS n * kTup n * Fintype.card (InnerCoord n)) +
      (Fintype.card (InnerCoord n) : ℝ) * testFail E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)
  alpha : ∀ i, AlphaFacts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)

/-- P11.1a–b assembled: base labels with all slice facts. -/
theorem slice_facts :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ {N : ℕ} {E : Fin N → Fin N → Prop} {X Y : Finset (Fin N)} {κ : ℝ}
      (M : Menu11 n N E X Y κ), ∃ y₀ : M.ι → Fin N, SliceFacts M y₀ := by
  obtain ⟨n₁, hrow⟩ := odd_row_facts
  obtain ⟨n₂, hsig⟩ := sigma_fail
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn N E X Y κ M
  have hn₁ : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_right _ _) hn
  have hg : (0 : ℝ) < 1 / 2 + 2 * gS n := by unfold gS; positivity
  have hdeg : ∀ i y, (M.ν i).w y ≠ 0 → 0 < colDeg E M.G (M.μ i) y :=
    fun i y hy => lt_of_lt_of_le hg (M.high i y hy)
  choose y₀ hy₀ using fun i =>
    base_label E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (hdeg i)
  have hR : ∀ i, RowFacts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)
      (Real.exp ((n : ℝ) / 50)) :=
    fun i => hrow n hn₁ E M.G (M.μ i) (M.ν i) (y₀ i) (M.ν_width i) (M.high i) (hy₀ i).1
  exact ⟨y₀, {
    base := fun i => (hy₀ i).1
    test := fun i => (hy₀ i).2
    rows := hR
    sigma := fun i => hsig n hn₂ E M.G (M.μ i) (M.ν i) (y₀ i) (M.μ_width i) (M.high i) (hy₀ i).1
    alpha := fun i => alpha_facts E M.G (InnerCoord n) (kTup n) (gS n) (M.μ i) (M.ν i) (y₀ i)
      (hR i).row_nonneg (hR i).row_sum }⟩

end HypercubeRamsey.S11.Core
