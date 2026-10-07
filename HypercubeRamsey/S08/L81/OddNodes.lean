import HypercubeRamsey.S08.L81.AnchorNodes
import HypercubeRamsey.Tools.ScatteredUnion

/-!
# Lemma 8.1, Step 11: odd loads by successive removal of constraints

Source: `sections/08-…tex`, lines 395–422 (L8.1k).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

/-- The odd-moment constant `2(33K + 1)` (08:404–411). -/
def oddM (K : ℝ) : ℝ := 2 * (33 * K + 1)

namespace Ctx

variable {η₀ β p : ℝ} {h : ℕ} (D : Ctx η₀ β p h)

/-- L8.1k, anchor stage (08:398–400): at a successful history, separated odd rows under the anchor law are bounded by
`2^l` times the raw-anchor mean of the products of `N p⁰/.98`. -/
def OddAnchorStep : Prop :=
  ∀ q : D.Pre, D.Good q → ∀ (y : Fin D.N) (l : ℕ), l ≤ D.n → ∀ u : Fin l → OddRole D.n,
    (∀ i j, i ≠ j → 8 < keyDist (keyOf η₀ (u i).1) (keyOf η₀ (u j).1)) →
    (D.anchorLaw q).expect (fun W => ∏ i, (D.N : ℝ) * D.prow q W (cellOf η₀ (u i).1) y) ≤
      2 ^ l * (D.rawAnchors q).expect (fun W => ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100))

/-- L8.1k, hidden stage (08:401–411): the pre-anchor mean of the raw-anchor products is at most `C^l`. -/
def OddHiddenStep (C : ℝ) : Prop :=
  ∀ (y : Fin D.N) (l : ℕ), l ≤ D.n → ∀ u : Fin l → OddRole D.n,
    (∀ i j, i ≠ j → 8 < keyDist (keyOf η₀ (u i).1) (keyOf η₀ (u j).1)) →
    D.preLaw.expect (fun q => (if D.Good q then 1 else 0) *
      (D.rawAnchors q).expect (fun W => ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100))) ≤ C ^ l

end Ctx

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-- L8.1k(i) (08:398–400): `p ≤ p⁰/.98` pointwise (`PRowFacts`; `p = 0` off validity).  One anchor is touched by
`O(n^2)` grouped events, so removing the events touching the at most `2s l` cross anchors of the rows costs
`(1 - x_A)^{-O(s n^2 l)} ≤ 2^l` (`CondProductBound`); the integrand reads only those cross anchors (`P0Local`),
which then have their independent raw laws. -/
theorem odd_anchor_step (cA : ℝ) (hcA : 0 < cA) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → CondProductBound →
      (∀ q : D.Pre, D.Good q → D.AnchorLLL q (2 * Real.exp (-(D.n : ℝ) ^ cA))) →
      D.P0Local → D.PRowFacts → D.OddAnchorStep := by
  classical
  have hExpRatio : Filter.Tendsto
      (fun n : ℕ => Real.exp ((n : ℝ) ^ cA) / ((n : ℝ) ^ cA) ^ (Nat.ceil (5 / cA) + 1))
      Filter.atTop Filter.atTop := by
    have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ cA) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hcA).comp tendsto_natCast_atTop_atTop
    exact (Real.tendsto_exp_div_pow_atTop (Nat.ceil (5 / cA) + 1)).comp ht
  have hExpEvent : ∀ᶠ n : ℕ in Filter.atTop,
      6000 * (n : ℝ) ^ (5 : ℕ) ≤ Real.exp ((n : ℝ) ^ cA) := by
    have hratio := hExpRatio.eventually (Filter.eventually_ge_atTop (6000 : ℝ))
    have hone := Filter.eventually_ge_atTop (1 : ℕ)
    filter_upwards [hratio, hone] with n hratio hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hceil : 5 / cA ≤ (Nat.ceil (5 / cA) : ℝ) := Nat.le_ceil _
    have hk : 5 ≤ cA * ((Nat.ceil (5 / cA) + 1 : ℕ) : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hceil hcA.le
      have hcancel : cA * (5 / cA) = 5 := by field_simp [ne_of_gt hcA]
      rw [hcancel] at hmul
      have hceilUp : cA * (Nat.ceil (5 / cA) : ℝ) ≤
          cA * ((Nat.ceil (5 / cA) + 1 : ℕ) : ℝ) := by
        have hceilNat : Nat.ceil (5 / cA) ≤ Nat.ceil (5 / cA) + 1 := by omega
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast hceilNat) hcA.le
      linarith
    have htPos : 0 < (n : ℝ) ^ cA := Real.rpow_pos_of_pos hnR _
    have hpow : ((n : ℝ) ^ cA) ^ (Nat.ceil (5 / cA) + 1) =
        (n : ℝ) ^ (cA * ((Nat.ceil (5 / cA) + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hnR.le cA _).symm
    have hfive : (n : ℝ) ^ (5 : ℕ) ≤
        ((n : ℝ) ^ cA) ^ (Nat.ceil (5 / cA) + 1) := by
      rw [← Real.rpow_natCast (n : ℝ) 5, hpow]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hk
    have hden : 0 < ((n : ℝ) ^ cA) ^ (Nat.ceil (5 / cA) + 1) :=
      pow_pos htPos _
    have hscaled : 6000 * ((n : ℝ) ^ cA) ^ (Nat.ceil (5 / cA) + 1) ≤
        Real.exp ((n : ℝ) ^ cA) := (le_div_iff₀ hden).mp hratio
    exact (mul_le_mul_of_nonneg_left hfive (by norm_num : (0 : ℝ) ≤ 6000)).trans hscaled
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (hExpEvent.and (Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩))
  refine ⟨n₀, ?_⟩
  intro D hn hGrid hCP hAnchor hLoc hP
  have hLarge := hn₀ D.n hn
  have hnNat : 1 ≤ D.n := hLarge.2
  have hnR : 1 ≤ (D.n : ℝ) := by exact_mod_cast hnNat
  have hnPos : 0 < (D.n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hτ : tau8 η₀ ≤ 1 := by
    rw [tau8_eq]
    unfold eta8
    have hmin := min_le_right (η₀ / 2) (4 / 100 : ℝ)
    linarith
  have hsBound : sC η₀ D.n ≤ D.n := by
    apply Nat.ceil_le.mpr
    calc
      (D.n : ℝ) ^ tau8 η₀ ≤ (D.n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnR hτ
      _ = D.n := by rw [Real.rpow_one]
  have hdBound : dC η₀ D.n ≤ D.n := by
    have := hGrid.split
    unfold mC at this
    unfold dC
    omega
  let deg : ℕ := (2 * sC η₀ D.n + dC η₀ D.n + 1) ^ 4
  let M : ℕ := 2 * sC η₀ D.n * (deg + 1)
  have hdegBase : 2 * sC η₀ D.n + dC η₀ D.n + 1 ≤ 5 * D.n := by omega
  have hdegBound : deg ≤ (5 * D.n) ^ 4 := by
    dsimp [deg]
    exact Nat.pow_le_pow_left hdegBase 4
  have hMany : 8 * (sC η₀ D.n : ℝ) * ((deg : ℝ) + 1) ≤ 6000 * (D.n : ℝ) ^ 5 := by
    have hdegR : (deg : ℝ) ≤ ((5 * D.n) ^ 4 : ℕ) := by exact_mod_cast hdegBound
    have hsR : (sC η₀ D.n : ℝ) ≤ D.n := by exact_mod_cast hsBound
    have hnR' : (1 : ℝ) ≤ D.n := hnR
    have hcastPow : (((5 * D.n) ^ 4 : ℕ) : ℝ) = 625 * (D.n : ℝ) ^ 4 := by
      push_cast
      ring
    have hpol : 8 * (D.n : ℝ) * (((5 * D.n) ^ 4 : ℕ) + 1) ≤
        6000 * (D.n : ℝ) ^ 5 := by
      rw [hcastPow]
      have hn4 : 1 ≤ (D.n : ℝ) ^ (4 : ℕ) := by
        calc
          1 = (1 : ℝ) ^ (4 : ℕ) := by norm_num
          _ ≤ (D.n : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hnR 4
      have hn5 : (D.n : ℝ) ≤ (D.n : ℝ) ^ 5 := by
        calc
          (D.n : ℝ) = (D.n : ℝ) * 1 := by ring
          _ ≤ (D.n : ℝ) * (D.n : ℝ) ^ 4 :=
            mul_le_mul_of_nonneg_left hn4 (by positivity)
          _ = (D.n : ℝ) ^ 5 := by ring
      nlinarith
    calc
      8 * (sC η₀ D.n : ℝ) * ((deg : ℝ) + 1) ≤
          8 * (D.n : ℝ) * (((5 * D.n) ^ 4 : ℕ) + 1) := by gcongr
      _ ≤ 6000 * (D.n : ℝ) ^ 5 := hpol
  have hExpLarge : 6000 * (D.n : ℝ) ^ 5 ≤ Real.exp ((D.n : ℝ) ^ cA) := hLarge.1
  have hxM : (2 * Real.exp (-((D.n : ℝ) ^ cA))) * (M : ℝ) ≤ 1 / 2 := by
    have hratio : 8 * (sC η₀ D.n : ℝ) * ((deg : ℝ) + 1) ≤
        Real.exp ((D.n : ℝ) ^ cA) := hMany.trans hExpLarge
    have hscaled := mul_le_mul_of_nonneg_right hratio
      (inv_nonneg.mpr (Real.exp_pos ((D.n : ℝ) ^ cA)).le)
    have hscaled' : 8 * (sC η₀ D.n : ℝ) * ((deg : ℝ) + 1) *
        (Real.exp ((D.n : ℝ) ^ cA))⁻¹ ≤ 1 := by
      simpa [mul_assoc] using hscaled
    have hMcast : (M : ℝ) = 2 * (sC η₀ D.n : ℝ) * ((deg : ℝ) + 1) := by
      simp [M, Nat.cast_mul, Nat.cast_add]
    calc
      (2 * Real.exp (-((D.n : ℝ) ^ cA))) * (M : ℝ) =
          4 * (sC η₀ D.n : ℝ) * ((deg : ℝ) + 1) *
            (Real.exp ((D.n : ℝ) ^ cA))⁻¹ := by
              rw [hMcast, Real.exp_neg]
              ring
      _ ≤ 1 / 2 := by nlinarith [hscaled']
  have hP0marg (Q : FinProb D.Tup) (y : Fin D.N) :
      0 ≤ averageCoordinateMarginal Q y := by
    unfold averageCoordinateMarginal
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun i _ => pr_nonneg Q (fun ω => ω i = y))
  have hP0light (Q : FinProb D.Tup) : 0 ≤ D.lightMass Q := by
    unfold Ctx.lightMass
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (hP0marg Q y) (by split_ifs <;> norm_num)
  have hp0nonneg (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) :
      0 ≤ D.p0 q W c y := by
    unfold Ctx.p0
    split_ifs with hpv
    · unfold Ctx.p0w
      by_cases hzero : D.lightMass (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) = 0
      · simp [hzero]
      · have hmass := hP0light (D.selPost q.1.1 q.1.2 c (D.presOf q W c))
        have hpos : 0 < D.lightMass (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) := by
          by_contra hn'
          exact hzero (le_antisymm (le_of_not_gt hn') hmass)
        simp only [if_neg hzero]
        apply div_nonneg
        · have hflag : 0 ≤ (if y ∈ heavyCoordinateSet
              (D.selPost q.1.1 q.1.2 c (D.presOf q W c)) D.heavyB then 0 else 1 : ℝ) := by
            split_ifs <;> norm_num
          exact mul_nonneg (hP0marg _ y) hflag
        · exact hpos.le
    · exact le_rfl
  have hrowBound (q : D.Pre) (W : D.Anch) (c : D.CellT) (y : Fin D.N) :
      (D.N : ℝ) * D.prow q W c y ≤ (D.N : ℝ) * D.p0 q W c y / (98 / 100) := by
    by_cases hv : D.Valid8 q W c
    · have hrow := (hP q W c).2.2 hv |>.2.1 y
      calc
        (D.N : ℝ) * D.prow q W c y ≤ (D.N : ℝ) * (D.p0 q W c y / (98 / 100)) :=
          mul_le_mul_of_nonneg_left hrow (by positivity)
        _ = (D.N : ℝ) * D.p0 q W c y / (98 / 100) := by ring
    · simp only [Ctx.prow, if_neg hv, mul_zero]
      exact div_nonneg (mul_nonneg (by positivity) (hp0nonneg q W c y)) (by norm_num)
  refine fun q hq y l hl u hsep => ?_
  let c : Fin l → D.CellT := fun i => cellOf η₀ (u i).1
  let U : Finset D.CellT := Finset.univ.biUnion fun i : Fin l =>
    (crossKeys (c i).1).image fun g => (g, (c i).2)
  let row (W : D.Anch) : ℝ := ∏ i, (D.N : ℝ) * D.prow q W (c i) y
  let psi (W : D.Anch) : ℝ := ∏ i, (D.N : ℝ) * D.p0 q W (c i) y / (98 / 100)
  have hUcoord (i : Fin l) (g : D.KeyT) (hg : g ∈ crossKeys (c i).1) :
      (g, (c i).2) ∈ U := by
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
  have hpsiDepends : FinProb.DependsOn psi U := by
    intro W W' hWW
    dsimp [psi]
    apply Finset.prod_congr rfl
    intro i hi
    have hp0eq := hLoc q q W W' (c i)
      (by intro g hg; rfl)
      (by intro g hg; exact ⟨rfl, rfl⟩)
      (by intro g hg; exact ⟨rfl, rfl⟩)
      (by intro g hg; exact hWW (g, (c i).2) (hUcoord i g hg))
    rw [hp0eq]
  have hrowPsi (W : D.Anch) : row W ≤ psi W := by
    dsimp [row, psi]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact mul_nonneg (by positivity) ((hP q W (c i)).1 y)
    · intro i hi
      exact hrowBound q W (c i) y
  have hpsiNonneg (W : D.Anch) : 0 ≤ psi W := by
    dsimp [psi]
    apply Finset.prod_nonneg
    intro i hi
    exact div_nonneg (mul_nonneg (by positivity) (hp0nonneg q W (c i) y)) (by norm_num)
  let avoid (W : D.Anch) : Prop := ∀ c, ¬ D.CellBad q W c
  let phi (W : D.Anch) : ℝ := if avoid W then row W else 0
  have hphiNonneg : ∀ W, 0 ≤ phi W := by
    intro W
    by_cases hv : avoid W
    · simp [phi, hv]
      dsimp [row]
      apply Finset.prod_nonneg
      intro i hi
      exact mul_nonneg (by positivity) ((hP q W (c i)).1 y)
    · simp [phi, hv]
  have hphiPsi (W : D.Anch) : phi W ≤ psi W := by
    by_cases hv : avoid W
    · simpa [phi, hv] using hrowPsi W
    · simpa [phi, hv] using hpsiNonneg W
  have hUcard : U.card ≤ l * (2 * sC η₀ D.n) := by
    calc
      U.card ≤ ∑ i : Fin l, ((crossKeys (c i).1).image fun g => (g, (c i).2)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ i : Fin l, 2 * sC η₀ D.n := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ((crossKeys (c i).1).image fun g => (g, (c i).2)).card ≤
              (crossKeys (c i).1).card := Finset.card_image_le
          _ ≤ 2 * sC η₀ D.n := by exact_mod_cast hGrid.crossKeys_card _
      _ = _ := by simp
  let touching : Finset D.CellT := Finset.univ.filter fun e : D.CellT => ¬ Disjoint (cellBall e 2) U
  have hTouched :
      (Finset.univ.filter fun e : D.CellT => ¬ Disjoint (cellBall e 2) U).card ≤
        U.card * (deg + 1) := by
    have hsub : touching ⊆ U.biUnion fun v : D.CellT =>
        insert v (Finset.univ.filter fun j : D.CellT => j ≠ v ∧
          ¬ Disjoint (cellBall v 2) (cellBall j 2)) := by
      intro e he
      have he' := (Finset.mem_filter.mp he).2
      rcases Finset.not_disjoint_iff.mp he' with ⟨v, hvE, hvU⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨v, hvU, ?_⟩
      by_cases hev : e = v
      · simp [hev]
      · simp only [Finset.mem_insert]
        right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hev, ?_⟩
        apply Finset.not_disjoint_iff.mpr
        refine ⟨v, ?_, hvE⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change cellDist v v ≤ 2
        unfold cellDist keyDist
        simp [_root_.hammingDist_self]
    calc
      (Finset.univ.filter fun e : D.CellT => ¬ Disjoint (cellBall e 2) U).card = touching.card := rfl
      _ ≤ (U.biUnion fun v : D.CellT =>
          insert v (Finset.univ.filter fun j : D.CellT => j ≠ v ∧
            ¬ Disjoint (cellBall v 2) (cellBall j 2))).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ U, (insert v (Finset.univ.filter fun j : D.CellT => j ≠ v ∧
            ¬ Disjoint (cellBall v 2) (cellBall j 2))).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ U, (deg + 1) := by
        apply Finset.sum_le_sum
        intro v hv
        have hdeg := (hAnchor q hq).degree v
        have hcard : (Finset.univ.filter fun j : D.CellT => j ≠ v ∧
            ¬ Disjoint (cellBall v 2) (cellBall j 2)).card ≤ deg := by
          simpa [Ctx.AnchorLLL, deg] using hdeg
        exact le_trans (Finset.card_insert_le v _) (Nat.add_le_add_right hcard 1)
      _ = U.card * (deg + 1) := by simp
  have hTouchCount : Finset.card touching ≤ l * M := by
    calc
      Finset.card touching ≤ U.card * (deg + 1) := by simpa [touching] using hTouched
      _ ≤ (l * (2 * sC η₀ D.n)) * (deg + 1) :=
        Nat.mul_le_mul_right (deg + 1) hUcard
      _ = l * M := by simp [M, Nat.mul_assoc]
  let x : ℝ := 2 * Real.exp (-((D.n : ℝ) ^ cA))
  have hLLL := hAnchor q hq
  have hxNonneg : 0 ≤ x := by positivity
  have hxlt : x < 1 := by simpa [x] using hLLL.x_lt_one
  have hbasePos : 0 < 1 - x := sub_pos.mpr hxlt
  have hbaseLe : 1 - x ≤ 1 := by linarith [hxNonneg]
  have hBern : (1 / 2 : ℝ) ≤ (1 - x) ^ M := by
    have hb := one_add_mul_sub_le_pow (a := 1 - x) (by linarith) M
    nlinarith [hxM, hb]
  have hbasePow : (1 / 2 : ℝ) ^ l ≤ ((1 - x) ^ M) ^ l :=
    pow_le_pow_left₀ (by norm_num) hBern l
  have hTouchCount' : Finset.card touching ≤ M * l := by
    exact hTouchCount.trans (Nat.le_of_eq (Nat.mul_comm l M))
  have hpowOrder : (1 - x) ^ (M * l) ≤ (1 - x) ^ Finset.card touching := by
    apply pow_le_pow_of_le_one hbasePos.le hbaseLe hTouchCount'
  have hcost : ((1 - x) ^ Finset.card touching)⁻¹ ≤ (2 : ℝ) ^ l := by
    calc
      ((1 - x) ^ Finset.card touching)⁻¹ ≤ ((1 - x) ^ (M * l))⁻¹ :=
        (inv_le_inv₀ (pow_pos hbasePos _) (pow_pos hbasePos _)).2 hpowOrder
      _ = (((1 - x) ^ M) ^ l)⁻¹ := by rw [pow_mul]
      _ ≤ ((1 / 2 : ℝ) ^ l)⁻¹ :=
        (inv_le_inv₀ (pow_pos (pow_pos hbasePos _) _) (pow_pos (by norm_num : (0 : ℝ) < (1 / 2 : ℝ)) _)).2
          hbasePow
      _ = (2 : ℝ) ^ l := by
        rw [div_pow]
        norm_num
  let P : D.CellT → FinProb (Fin D.N) := fun c => D.Usel q c
  let B : ℝ := (D.rawAnchors q).expect psi
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    unfold FinProb.expect
    apply Finset.sum_nonneg
    intro W hW
    exact mul_nonneg ((D.rawAnchors q).nonneg W) (hpsiNonneg W)
  have hMarginal (ω : D.Anch) :
      (D.rawAnchors q).expect psi =
        (FinProb.pi (fun v : U => P v.1)).expect (fun a => psi (glue U ω a)) := by
    have hEqFun (W : D.Anch) :
        psi W = psi (glue U ω (fun v : U => W v.1)) := by
      apply hpsiDepends W _
      intro v hv
      simp [glue, hv]
    change (FinProb.pi P).expect psi = _
    calc
      (FinProb.pi P).expect psi =
          (FinProb.pi P).expect (fun W => psi (glue U ω (fun v : U => W v.1))) := by
            unfold FinProb.expect
            apply Finset.sum_congr rfl
            intro W hW
            rw [hEqFun W]
      _ = (FinProb.pi (fun v : U => P v.1)).expect (fun a => psi (glue U ω a)) :=
        FinProb.pi_marginal_expect P U (fun a => psi (glue U ω a))
  have hBound (ω : D.Anch) :
      (∑ a : (∀ v : U, Fin D.N),
        (∏ v : U, (D.Usel q v.1).w (a v)) * phi (glue U ω a)) ≤ B := by
    calc
      _ ≤ ∑ a : (∀ v : U, Fin D.N),
          (∏ v : U, (D.Usel q v.1).w (a v)) * psi (glue U ω a) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hphiPsi (glue U ω a))
          (Finset.prod_nonneg fun v hv => (D.Usel q v.1).nonneg (a v))
      _ = (FinProb.pi (fun v : U => P v.1)).expect (fun a => psi (glue U ω a)) := by
        simp [FinProb.expect, FinProb.pi, P]
      _ = B := by
        rw [← hMarginal ω]
  unfold CondProductBound at hCP
  have hCondPair := hCP P (fun c W => D.CellBad q W c) (fun c => cellBall c 2)
    x deg hLLL
  have hCond := hCondPair.2 U phi hphiNonneg B hBound
  have hAvoidPos : 0 < (D.rawAnchors q).pr (avoid) := by
    simpa [Ctx.rawAnchors, P, avoid] using hCondPair.1
  have hAnchorExpect :
      (D.anchorLaw q).expect row = (condOr (D.rawAnchors q) avoid).expect phi := by
    change (condOr (D.rawAnchors q) avoid).expect row = _
    unfold condOr
    rw [dif_pos hAvoidPos]
    unfold FinProb.expect FinProb.cond
    apply Finset.sum_congr rfl
    intro W hW
    by_cases ha : avoid W <;> simp [phi, ha]
  have hRawExpect : (D.rawAnchors q).expect psi = B := rfl
  calc
    (D.anchorLaw q).expect row = (condOr (D.rawAnchors q) avoid).expect phi := hAnchorExpect
    _ ≤ ((1 - x) ^ Finset.card touching)⁻¹ * B := by
      simpa [Ctx.rawAnchors, P, avoid, x, Ctx.anchorLaw, touching] using hCond
    _ ≤ (2 : ℝ) ^ l * (D.rawAnchors q).expect psi := by
      rw [hRawExpect]
      exact mul_le_mul_of_nonneg_right hcost hBnonneg

/-- L8.1k(ii) (08:401–411): discard global selection success (validity stays inside `p⁰`); conditional on positions
and hidden tuples the rows read disjoint tags, activations, ties and cross anchors (grid scopes of radius three,
keys more than eight apart, `P0Local`), so the raw means factor; remove the at most `(2s+1)^2` hidden events
touching each target tuple (`(1 - x_H)^{-(2s+1)^2} ≤ 2` per row, `CondProductBound`); the targets then have their
independent priors and each factor is the raw mean of Step 7, at most `16K/(.98)` after normalization. -/
theorem odd_hidden_step (cH : ℝ) (hcH : 0 < cH) (hη₀ : 0 < η₀) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → GridFacts η₀ D.n → CondProductBound →
      D.HiddenLLL (2 * Real.exp (-(D.n : ℝ) ^ cH)) → D.P0Local → D.P0RawMean K → D.P0Law →
      D.OddHiddenStep (33 * K + 1) := by
  sorry

/-- L8.1k, assembly of the two stages (08:396–413): the staged law draws the anchors from the anchor law at each
pre-anchor history, so the joint moment is the pre-anchor mean of the anchor-law means. -/
theorem odd_moment (D : Ctx η₀ β p h) (C : ℝ) (hC : 0 ≤ C) (hA : D.OddAnchorStep) (hH : D.OddHiddenStep C)
    (hP : D.PRowFacts) : D.OddMoment (2 * C) := by
  classical
  intro y l hl u hsep
  have hExpand :
      D.stagedLaw.expect (fun z => (if D.Good z.1 then 1 else 0) *
        ∏ i, (D.N : ℝ) * D.prow z.1 z.2 (cellOf η₀ (u i).1) y) =
      ∑ q, D.preLaw.w q * (D.anchorLaw q).expect (fun W => (if D.Good q then 1 else 0) *
        ∏ i, (D.N : ℝ) * D.prow q W (cellOf η₀ (u i).1) y) := by
    simpa only [Ctx.stagedLaw] using
      (FinProb.bind_expect D.preLaw D.anchorLaw (fun q W => (if D.Good q then 1 else 0) *
        ∏ i, (D.N : ℝ) * D.prow q W (cellOf η₀ (u i).1) y))
  rw [hExpand]
  have hAnchor (q : D.Pre) :
      (D.anchorLaw q).expect (fun W => (if D.Good q then 1 else 0) *
        ∏ i, (D.N : ℝ) * D.prow q W (cellOf η₀ (u i).1) y) ≤
        2 ^ l * (if D.Good q then
          (D.rawAnchors q).expect (fun W =>
            ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100)) else 0) := by
    by_cases hG : D.Good q
    · simpa [hG] using hA q hG y l hl u hsep
    · simp [hG, FinProb.expect]
  calc
    (∑ q, D.preLaw.w q *
        (D.anchorLaw q).expect (fun W => (if D.Good q then 1 else 0) *
          ∏ i, (D.N : ℝ) * D.prow q W (cellOf η₀ (u i).1) y))
        ≤ ∑ q, D.preLaw.w q *
          (2 ^ l * (if D.Good q then
            (D.rawAnchors q).expect (fun W =>
              ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100)) else 0)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left (hAnchor q) (D.preLaw.nonneg q)
    _ = 2 ^ l * D.preLaw.expect (fun q => (if D.Good q then 1 else 0) *
          (D.rawAnchors q).expect (fun W =>
            ∏ i, (D.N : ℝ) * D.p0 q W (cellOf η₀ (u i).1) y / (98 / 100))) := by
      simp only [FinProb.expect]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hG : D.Good q <;> simp [hG] <;> ring
    _ ≤ 2 ^ l * C ^ l := by
      exact mul_le_mul_of_nonneg_left (hH y l hl u hsep) (by positivity)
    _ = (2 * C) ^ l := by rw [mul_pow]

/-- L8.1k(iii) (08:415–422): Lemma 3.6 with labels for the odd rows on success: near rows have keys within distance
eight (fraction `f_grid`), the cap is `e^{.02 s log n}` and `n f_grid e^{.02 s log n} ≤ 1`; separated moments are
at most `C^l` (`OddMoment`); so the normalized average odd load exceeds `4(C+1)` with probability at most
`n 2^n 4^{-n}`, and otherwise the column sums are at most `2^{n-1} 4(C+1)/N ≤ 10⁻⁸`. -/
theorem odd_tail (C : ℝ) (hC : 0 ≤ C) (hη₀ : 0 < η₀) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → (10 : ℝ) ^ 8 * (4 * (C + 1)) * 2 ^ D.n ≤ D.N → D.PRowFacts → D.OddMoment C →
      D.stagedLaw.pr (fun z => D.Good z.1 ∧ ∃ y, (1e-8 : ℝ) < D.oddCol z.1 z.2 y) ≤
        (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
  classical
  have htau : 0 < tau8 η₀ := tau8_pos hη₀
  have hsEvent : ∀ᶠ n : ℕ in Filter.atTop, 1000 < (n : ℝ) ^ tau8 η₀ := by
    have ht := (tendsto_rpow_atTop htau).comp tendsto_natCast_atTop_atTop
    exact ht.eventually_gt_atTop 1000
  have hpowEvent : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ (n : ℝ) ^ (1 / 100 : ℝ) := by
    have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  have hnEvent : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ (n : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast hn
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hsEvent.and (hpowEvent.and hnEvent))
  refine ⟨n₀, ?_⟩
  intro D hn X Y R hStd hGrid hN hP hM
  have hLarge := hn₀ D.n hn
  have hnR : 1 ≤ (D.n : ℝ) := hLarge.2.2
  have hnPos : 0 < (D.n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  let s : ℕ := sC η₀ D.n
  have hsLarge : 1000 < (s : ℝ) := by
    have hc : (D.n : ℝ) ^ tau8 η₀ ≤ (s : ℝ) := by
      dsimp [s, sC]
      exact Nat.le_ceil _
    exact lt_of_lt_of_le hLarge.1 hc
  have hpow (a : ℝ) : ((D.n : ℝ) ^ a) ^ s = (D.n : ℝ) ^ (a * (s : ℝ)) := by
    rw [← Real.rpow_natCast ((D.n : ℝ) ^ a) s]
    exact (Real.rpow_mul hnPos.le a (s : ℝ)).symm
  have hExp : Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n) =
      (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ)) := by
    calc
      Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n) =
          Real.exp (Real.log D.n * ((2 / 100 : ℝ) * (s : ℝ))) := by congr 1 <;> ring
      _ = (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ)) :=
        (Real.rpow_def_of_pos hnPos _).symm
  have hFactor :
      (D.n : ℝ) * fGrid η₀ D.n * Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n) =
      (D.n : ℝ) ^ (10 : ℕ) *
          ((2 : ℝ) ^ s * (D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ)) *
            (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ))) := by
    unfold fGrid
    change (D.n : ℝ) * ((D.n : ℝ) ^ (9 : ℕ) *
      (2 * (D.n : ℝ) ^ (-(4 / 100 : ℝ))) ^ s) *
        Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n) = _
    rw [mul_pow, hpow (-(4 / 100 : ℝ)), hExp]
    have hn10 : (D.n : ℝ) * (D.n : ℝ) ^ (9 : ℕ) = (D.n : ℝ) ^ (10 : ℕ) := by ring
    calc
      _ = ((D.n : ℝ) * (D.n : ℝ) ^ (9 : ℕ)) *
          ((2 : ℝ) ^ s * (D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ)) *
            (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ))) := by ring
      _ = _ := by rw [hn10]
  have htwo : 2 ≤ (D.n : ℝ) ^ (1 / 100 : ℝ) := hLarge.2.1
  have hpowBound :
      (2 : ℝ) ^ s * (D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ)) *
        (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ)) ≤
        (D.n : ℝ) ^ (-(1 / 100 : ℝ) * (s : ℝ)) := by
    have htwoPow : (2 : ℝ) ^ s ≤ (D.n : ℝ) ^ ((1 / 100 : ℝ) * (s : ℝ)) := by
      calc
        (2 : ℝ) ^ s ≤ ((D.n : ℝ) ^ (1 / 100 : ℝ)) ^ s :=
          pow_le_pow_left₀ (by norm_num) htwo s
        _ = (D.n : ℝ) ^ ((1 / 100 : ℝ) * (s : ℝ)) := hpow _
    have hcombine :
        (D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ)) *
          (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ)) =
          (D.n : ℝ) ^ (-(2 / 100 : ℝ) * (s : ℝ)) := by
      calc
        _ = (D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ) + (2 / 100 : ℝ) * (s : ℝ)) :=
          (Real.rpow_add hnPos _ _).symm
        _ = _ := by congr 1 <;> ring
    calc
      _ = (2 : ℝ) ^ s * ((D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ)) *
          (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ))) := by ring
      _ = (2 : ℝ) ^ s * (D.n : ℝ) ^ (-(2 / 100 : ℝ) * (s : ℝ)) := by rw [hcombine]
      _ ≤ (D.n : ℝ) ^ ((1 / 100 : ℝ) * (s : ℝ)) *
          (D.n : ℝ) ^ (-(2 / 100 : ℝ) * (s : ℝ)) :=
            mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hnPos.le _)
      _ = (D.n : ℝ) ^ (-(1 / 100 : ℝ) * (s : ℝ)) := by
        rw [← Real.rpow_add hnPos]
        congr 1 <;> ring
  have hexpBound :
      (D.n : ℝ) ^ (-(1 / 100 : ℝ) * (s : ℝ)) ≤ (D.n : ℝ) ^ (-(10 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le hnR
    nlinarith
  have hPowerCancel : (D.n : ℝ) ^ (10 : ℕ) * (D.n : ℝ) ^ (-(10 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast (D.n : ℝ) 10, ← Real.rpow_add hnPos]
    norm_num
  have hsmall : (D.n : ℝ) * fGrid η₀ D.n *
      Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n) ≤ 1 := by
    calc
      _ = (D.n : ℝ) ^ (10 : ℕ) *
          ((2 : ℝ) ^ s * (D.n : ℝ) ^ (-(4 / 100 : ℝ) * (s : ℝ)) *
            (D.n : ℝ) ^ ((2 / 100 : ℝ) * (s : ℝ))) := hFactor
      _ ≤ (D.n : ℝ) ^ (10 : ℕ) * (D.n : ℝ) ^ (-(1 / 100 : ℝ) * (s : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowBound (by positivity)
      _ ≤ (D.n : ℝ) ^ (10 : ℕ) * (D.n : ℝ) ^ (-(10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hexpBound (by positivity)
      _ = 1 := hPowerCancel
  let succ : Finset (D.Pre × D.Anch) := Finset.univ.filter fun z => D.Good z.1
  let Z : OddRole D.n → Fin D.N → (D.Pre × D.Anch) → ℝ :=
    fun u y z => (D.N : ℝ) * D.prow z.1 z.2 (cellOf η₀ u.1) y
  let near : OddRole D.n → Finset (OddRole D.n) := oddKeyNear η₀ 8
  let d : OddRole D.n → Fin D.N → ℝ := fun _ _ => 1
  have huCardPos : 0 < Fintype.card (OddRole D.n) := by
    rw [hGrid.odd_card]
    positivity
  letI : Nonempty (OddRole D.n) := Fintype.card_pos_iff.mp huCardPos
  have hZ0 : ∀ u y z, 0 ≤ Z u y z := by
    intro u y z
    exact mul_nonneg (by positivity) ((hP z.1 z.2 (cellOf η₀ u.1)).1 y)
  have hZL : ∀ u y z, z ∈ succ → Z u y z ≤
      Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n) := by
    intro u y z hz
    by_cases hv : D.Valid8 z.1 z.2 (cellOf η₀ u.1)
    · exact (hP z.1 z.2 (cellOf η₀ u.1)).2.2 hv |>.2.2 y
    · simp [Z, Ctx.prow, hv]
      positivity
  have hself : ∀ u, u ∈ near u := by
    intro u
    simp only [near, oddKeyNear, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold keyDist
    simp
  have hnear : ∀ u, ((near u).card : ℝ) ≤ fGrid η₀ D.n * Fintype.card (OddRole D.n) :=
    hGrid.near_odd
  have hkeyDistComm (g v : Key η₀ D.n) : keyDist g v = keyDist v g := by
    unfold keyDist
    apply Finset.sum_congr rfl
    intro r hr
    exact Nat.dist_comm _ _
  have hjoint : ∀ y (m : ℕ), m ≤ D.n → ∀ t : Fin m → OddRole D.n,
      (∀ i j, j < i → t i ∉ near (t j)) →
        (∑ z ∈ succ, D.stagedLaw.w z * ∏ i, Z (t i) y z) ≤
          (C + 1) ^ m * ∏ i, d (t i) y := by
    intro y m hm t hsep
    have hkeySep : ∀ i j, i ≠ j →
        8 < keyDist (keyOf η₀ (t i).1) (keyOf η₀ (t j).1) := by
      intro i j hij
      by_cases hji : j < i
      · by_contra hn
        have hmem : t i ∈ near (t j) := by
          simp only [near, oddKeyNear, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        exact hsep i j hji hmem
      · have hij' : i < j := by omega
        have hnot := hsep j i hij'
        by_contra hn
        have hd : keyDist (keyOf η₀ (t i).1) (keyOf η₀ (t j).1) ≤ 8 := by omega
        have hmem : t j ∈ near (t i) := by
          simp only [near, oddKeyNear, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hkeyDistComm]
          exact hd
        exact hnot hmem
    have hMomentSum :
        (∑ z ∈ succ, D.stagedLaw.w z * ∏ i, Z (t i) y z) =
          D.stagedLaw.expect (fun z => (if D.Good z.1 then 1 else 0) *
            ∏ i, (D.N : ℝ) * D.prow z.1 z.2 (cellOf η₀ (t i).1) y) := by
      simp [succ, Z, FinProb.expect, Finset.sum_filter]
    have hMoment := hM y m hm t hkeySep
    calc
      _ ≤ C ^ m := by rw [hMomentSum]; exact hMoment
      _ ≤ (C + 1) ^ m * ∏ i, d (t i) y := by
        simpa [d] using
          (pow_le_pow_left₀ hC (by linarith : C ≤ C + 1) m)
  have hmean : ∀ y, (Fintype.card (OddRole D.n) : ℝ)⁻¹ *
      ∑ u, d u y ≤ 1 := by
    intro y
    calc
      _ = (Fintype.card (OddRole D.n) : ℝ)⁻¹ *
          (Fintype.card (OddRole D.n) : ℝ) := by simp [d]
      _ = 1 := by field_simp [ne_of_gt (Nat.cast_pos.mpr huCardPos)]
      _ ≤ 1 := le_rfl
  have hlabels : (Fintype.card (Fin D.N) : ℝ) ≤ (D.n : ℝ) * 2 ^ D.n := by
    rw [Fintype.card_fin]
    exact_mod_cast hStd.size.2
  have hfGrid : 0 ≤ fGrid η₀ D.n := by
    unfold fGrid
    positivity
  have hScatter := scatteredMoments_union_labels D.stagedLaw succ Z hZ0
    (Real.exp ((2 / 100 : ℝ) * (s : ℝ) * Real.log D.n)) (by positivity) hZL
    near hself (fGrid η₀ D.n) hfGrid hnear D.n
    (by exact_mod_cast hGrid.pos.1) (C + 1) 1
    (by linarith) (by norm_num) d (by intros; norm_num) hmean hjoint hsmall hlabels
  have hpr : D.stagedLaw.pr (fun z => D.Good z.1 ∧ ∃ y,
      (1e-8 : ℝ) < D.oddCol z.1 z.2 y) ≤
      (∑ z, if z ∈ succ ∧ ∃ y,
        4 * (C + 1) * (1 + 1) <
          (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ∑ u, Z u y z then D.stagedLaw.w z else 0) := by
    unfold FinProb.pr
    apply Finset.sum_le_sum
    intro z hz
    by_cases hbad : D.Good z.1 ∧ ∃ y, (1e-8 : ℝ) < D.oddCol z.1 z.2 y
    · have hTarget := hbad
      obtain ⟨hG, y, hy⟩ := hbad
      have hsource : z ∈ succ ∧ ∃ y,
          4 * (C + 1) * (1 + 1) <
            (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ∑ u, Z u y z := by
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩, y, ?_⟩
        have hcard : (Fintype.card (OddRole D.n) : ℝ) = 2 ^ (D.n - 1) := by
          exact_mod_cast hGrid.odd_card
        have hnSub : D.n - 1 + 1 = D.n := Nat.sub_add_cancel hGrid.pos.1
        have hpowNat : (2 : ℝ) ^ D.n = (2 : ℝ) ^ (D.n - 1) * 2 := by
          calc
            (2 : ℝ) ^ D.n = (2 : ℝ) ^ (D.n - 1 + 1) := by
              exact congrArg (fun k : ℕ => (2 : ℝ) ^ k) hnSub.symm
            _ = (2 : ℝ) ^ (D.n - 1) * 2 := by rw [pow_succ]
        have hpow : (2 : ℝ) ^ D.n = (Fintype.card (OddRole D.n) : ℝ) * 2 := by
          calc
            _ = (2 : ℝ) ^ (D.n - 1) * 2 := hpowNat
            _ = _ := by rw [hcard]
        have hN' : (8 * (C + 1)) * (Fintype.card (OddRole D.n) : ℝ) ≤
            (D.N : ℝ) * (1e-8 : ℝ) := by
          have hNm := mul_le_mul_of_nonneg_right (show
            (10 : ℝ) ^ 8 * (4 * (C + 1)) * 2 ^ D.n ≤ D.N by exact hN)
            (by norm_num : (0 : ℝ) ≤ (1e-8 : ℝ))
          rw [hpow] at hNm
          norm_num at hNm
          nlinarith
        have hsumZ : ∑ u, Z u y z =
            (D.N : ℝ) * D.oddCol z.1 z.2 y := by
          simp [Z, Ctx.oddCol, ← Finset.mul_sum]
        rw [hsumZ]
        have hcardPos : 0 < (Fintype.card (OddRole D.n) : ℝ) := by exact_mod_cast huCardPos
        have hlow : 8 * (C + 1) ≤
            (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ((D.N : ℝ) * (1e-8 : ℝ)) := by
          calc
            8 * (C + 1) = (8 * (C + 1) * (Fintype.card (OddRole D.n) : ℝ)) *
                (Fintype.card (OddRole D.n) : ℝ)⁻¹ := by
                  field_simp [ne_of_gt hcardPos]
            _ ≤ ((D.N : ℝ) * (1e-8 : ℝ)) *
                (Fintype.card (OddRole D.n) : ℝ)⁻¹ :=
                  mul_le_mul_of_nonneg_right hN' (inv_nonneg.mpr hcardPos.le)
            _ = _ := by ring
        have hstrict : (Fintype.card (OddRole D.n) : ℝ)⁻¹ *
            ((D.N : ℝ) * (1e-8 : ℝ)) <
            (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ((D.N : ℝ) * D.oddCol z.1 z.2 y) := by
          apply mul_lt_mul_of_pos_left _ (inv_pos.mpr hcardPos)
          exact mul_lt_mul_of_pos_left hy (by exact_mod_cast hStd.size.1)
        nlinarith [hlow, hstrict]
      rw [if_pos hTarget, if_pos hsource]
    · rw [if_neg hbad]
      by_cases hs : z ∈ succ ∧ ∃ y, 4 * (C + 1) * (1 + 1) <
          (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ∑ u, Z u y z
      · rw [if_pos hs]
        exact D.stagedLaw.nonneg z
      · rw [if_neg hs]
  calc
    D.stagedLaw.pr (fun z => D.Good z.1 ∧ ∃ y, (1e-8 : ℝ) < D.oddCol z.1 z.2 y) ≤
    (∑ z, if z ∈ succ ∧ ∃ y,
        4 * (C + 1) * (1 + 1) <
          (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ∑ u, Z u y z then D.stagedLaw.w z else 0) := hpr
    _ ≤ (D.n : ℝ) * 2 ^ D.n * (1 / 4 : ℝ) ^ D.n := by
      convert hScatter using 1
      · apply Finset.sum_congr rfl
        intro z hz
        by_cases hs : z ∈ succ ∧ ∃ y,
            4 * (C + 1) * (1 + 1) <
              (Fintype.card (OddRole D.n) : ℝ)⁻¹ * ∑ u, Z u y z
        · simp [hs]
        · simp [hs]

end Nodes

end HypercubeRamsey.S08
