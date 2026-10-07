import HypercubeRamsey.Framework.LawLemmas
import HypercubeRamsey.S08.L81.Facts

/-!
# Lemma 8.1, Steps 2 and 4: base gates and the fixed-presentation reference experiment

Source: `sections/08-…tex`, lines 48–123 (L8.1c) and 139–176 (L8.1e).
-/

noncomputable section

namespace HypercubeRamsey.S08

open Classical OAI.HypercubeRamsey
open scoped BigOperators

theorem eta8_pos {η₀ : ℝ} (hη₀ : 0 < η₀) : 0 < eta8 η₀ := lt_min (by linarith) (by norm_num)

theorem tau8_pos {η₀ : ℝ} (hη₀ : 0 < η₀) : 0 < tau8 η₀ := by
  rw [tau8_eq]; exact div_pos (eta8_pos hη₀) (by norm_num)

section Nodes

variable (η₀ γ β p K : ℝ) (h : ℕ)

/-! ## L8.1c: base gates (08:76–123) -/

/-- L8.1c(G1) (08:83–89): the event `R'(Θ_g) < N^{-h} e^{-n^{τ/2}}` has probability at most `e^{-n^{τ/2}}` (there
are `N^h` tuples); outside it `η_g(i)/Λ(i) = ν_i^{⊗h}(Θ_g)/R'(Θ_g) ≤ e^{hn^β + n^{τ/2}}`, since `ν_i` has width
`n^β`. -/
theorem gate1_tail (hη₀ : 0 < η₀) (hβ₀ : 0 < β) :
    ∀ D : Ctx η₀ β p h, ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      ∀ g, D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) ≤ Real.exp (-(D.n : ℝ) ^ (tau8 η₀ / 2)) := by
  intro D X Y R hStd g
  let d : ℝ := Real.exp (-((D.n : ℝ) ^ (tau8 η₀ / 2))) / (D.N : ℝ) ^ h
  have hNNat : 0 < D.N := hStd.size.1
  have hNpos : 0 < (D.N : ℝ) := by exact_mod_cast hStd.size.1
  have hnNat : 0 < D.n := by
    by_contra hn
    have hn0 : D.n = 0 := Nat.eq_zero_of_not_pos hn
    have hNle0 : D.N ≤ 0 := by
      calc
        D.N ≤ D.n * 2 ^ D.n := hStd.size.2
        _ = 0 := by rw [hn0]; norm_num
    have hNzero : D.N = 0 := Nat.eq_zero_of_le_zero hNle0
    omega
  have hnPos : 0 < (D.n : ℝ) := by exact_mod_cast hnNat
  have hdpos : 0 < d := div_pos (Real.exp_pos _) (pow_pos hNpos _)
  have hcardTup : (Fintype.card D.Tup : ℝ) = (D.N : ℝ) ^ h := by
    simp [Ctx.Tup]
  have hcardMul : (Fintype.card D.Tup : ℝ) * d =
      Real.exp (-((D.n : ℝ) ^ (tau8 η₀ / 2))) := by
    dsimp [d]
    rw [hcardTup]
    field_simp [ne_of_gt hNpos]
  have hSmallProb : D.rawHidden.pr (fun Θ => D.R'.w (Θ g) < d) ≤
      Real.exp (-((D.n : ℝ) ^ (tau8 η₀ / 2))) := by
    let s : Finset D.KeyT := {g}
    let I := {u : D.KeyT // u ∈ s}
    let i₀ : I := ⟨g, by simp [s]⟩
    letI : Unique I := {
      default := i₀
      uniq := by
        intro i
        apply Subtype.ext
        have hi : i.1 = g := by
          exact Finset.mem_singleton.mp (by simpa [s] using i.2)
        exact hi
    }
    let A := ∀ i : I, D.Tup
    let P : D.KeyT → FinProb D.Tup := fun _ => D.R'
    let F : D.Hist → ℝ := fun Θ => if D.R'.w (Θ g) < d then 1 else 0
    let Pₛ : FinProb A := FinProb.pi (fun _ : I => D.R')
    let e : A ≃ D.Tup := Equiv.piUnique (fun _ : I => D.Tup)
    let ω₀ : D.Hist := fun _ => fun _ => ⟨0, hNNat⟩
    have hPrExpect : D.rawHidden.pr (fun Θ => D.R'.w (Θ g) < d) =
        D.rawHidden.expect F := by
      classical
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro Θ _
      by_cases he : D.R'.w (Θ g) < d <;> simp [F, he]
    have hdep : FinProb.DependsOn F s := by
      intro Θ Θ' hagree
      have hg := hagree g (by simp [s])
      simp [F, hg]
    have hpi := FinProb.pi_expect_depends P s F ω₀ hdep
    have hdefault : (default : I) = i₀ := Subsingleton.elim _ _
    have hig : (⟨g, by simp [s]⟩ : I) = i₀ := by
      apply Subtype.ext
      rfl
    have hMarg : D.rawHidden.pr (fun Θ => D.R'.w (Θ g) < d) =
        Pₛ.expect (fun a => if D.R'.w (a i₀) < d then 1 else 0) := by
      calc
        _ = D.rawHidden.expect F := hPrExpect
        _ = Pₛ.expect (fun a =>
            if D.R'.w (a ⟨g, by simp [s]⟩) < d then 1 else 0) := by
          simpa [Ctx.rawHidden, P, F, Pₛ, s, i₀,
            Equiv.piEquivPiSubtypeProd_symm_apply] using hpi
        _ = Pₛ.expect (fun a => if D.R'.w (a i₀) < d then 1 else 0) := by
          unfold FinProb.expect
          apply Finset.sum_congr rfl
          intro a _
          rw [hig]
    have hweight (a : ∀ i : I, D.Tup) : Pₛ.w a = D.R'.w (a i₀) := by
      change (∏ i : I, D.R'.w (a i)) = D.R'.w (a i₀)
      calc
        _ = ∏ i : I, D.R'.w (a i₀) := by
          apply Finset.prod_congr rfl
          intro i _
          rw [show i = i₀ from Subsingleton.elim _ _]
        _ = D.R'.w (a i₀) := by simp
    have hcard : (Fintype.card (∀ i : I, D.Tup) : ℝ) = (Fintype.card D.Tup : ℝ) := by
      have hc : Fintype.card (∀ i : I, D.Tup) = Fintype.card D.Tup := Fintype.card_congr e
      exact_mod_cast hc
    have hsumBound : Pₛ.expect (fun a => if D.R'.w (a i₀) < d then 1 else 0) ≤
        (Fintype.card (∀ i : I, D.Tup) : ℝ) * d := by
      change (∑ a : (∀ i : I, D.Tup), Pₛ.w a * if D.R'.w (a i₀) < d then 1 else 0) ≤
        (Fintype.card (∀ i : I, D.Tup) : ℝ) * d
      calc
        (∑ a : (∀ i : I, D.Tup), Pₛ.w a * if D.R'.w (a i₀) < d then 1 else 0) ≤
            ∑ a : (∀ i : I, D.Tup), if D.R'.w (a i₀) < d then d else 0 := by
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : D.R'.w (a i₀) < d
          · simp only [if_pos ha, mul_one]
            rw [hweight]
            exact le_of_lt ha
          · simp [ha]
        _ ≤ ∑ _a : (∀ i : I, D.Tup), d := by
          apply Finset.sum_le_sum
          intro a _
          by_cases ha : D.R'.w (a i₀) < d
          · simp [ha]
          · simp [ha, hdpos.le]
        _ = (Fintype.card (∀ i : I, D.Tup) : ℝ) * d := by
          simp [Finset.sum_const, nsmul_eq_mul]
    calc
      D.rawHidden.pr (fun Θ => D.R'.w (Θ g) < d) =
          Pₛ.expect (fun a => if D.R'.w (a i₀) < d then 1 else 0) := hMarg
      _ ≤ (Fintype.card (∀ i : I, D.Tup) : ℝ) * d := hsumBound
      _ = (Fintype.card D.Tup : ℝ) * d := by rw [hcard]
      _ = Real.exp (-((D.n : ℝ) ^ (tau8 η₀ / 2))) := hcardMul
  have hpowCap (i : D.M.ι) (θ : D.Tup) (hΛ : 0 < D.M.Λ i) :
      (∏ j, (D.M.ν i).w (θ j)) ≤ (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h := by
    obtain ⟨_, _, _, hνWidth, _⟩ := hStd.laws i hΛ
    calc
      (∏ j, (D.M.ν i).w (θ j)) ≤ ∏ j, Real.exp ((D.n : ℝ) ^ β) / D.N := by
        apply Finset.prod_le_prod₀
        · intro j _
          exact (D.M.ν i).nonneg (θ j)
        · intro j _
          exact hνWidth (θ j)
      _ = (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h := by
        simp [Finset.prod_const, div_pow]
  have hcapId : ((Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h) / d =
      Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) := by
    rw [div_pow, ← Real.exp_nat_mul]
    dsimp [d]
    field_simp [ne_of_gt hNpos, Real.exp_ne_zero]
    rw [← Real.exp_add]
    congr 1
    ring
  have hGateFromDen (Θ : D.Hist) (hr : d ≤ D.R'.w (Θ g)) : D.Gate1 Θ g := by
    intro i
    have hRpos : 0 < D.R'.w (Θ g) := lt_of_lt_of_le hdpos hr
    by_cases hΛ : 0 < D.M.Λ i
    · have hνprod := hpowCap i (Θ g) hΛ
      have hratio : (∏ j, (D.M.ν i).w ((Θ g) j)) / D.R'.w (Θ g) ≤
          ((Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h) / d := by
        apply (div_le_div_iff₀ hRpos hdpos).2
        calc
          (∏ j, (D.M.ν i).w ((Θ g) j)) * d ≤
              (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h * d :=
            mul_le_mul_of_nonneg_right hνprod hdpos.le
          _ ≤ (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h * D.R'.w (Θ g) :=
            mul_le_mul_of_nonneg_left hr (by positivity)
      have hpost : D.postW (Θ g) i =
          D.M.Λ i * (∏ j, (D.M.ν i).w ((Θ g) j)) / D.R'.w (Θ g) := by
        simp [Ctx.postW, ne_of_gt hRpos]
      calc
        D.postW (Θ g) i =
            D.M.Λ i * ((∏ j, (D.M.ν i).w ((Θ g) j)) / D.R'.w (Θ g)) := by
          rw [hpost]
          ring
        _ ≤ D.M.Λ i * (((Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h) / d) :=
          mul_le_mul_of_nonneg_left hratio (D.M.Λ_nonneg i)
        _ = Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * D.M.Λ i := by
          rw [hcapId]
          ring
    · have hΛzero : D.M.Λ i = 0 := by
        exact le_antisymm (le_of_not_gt hΛ) (D.M.Λ_nonneg i)
      simp [Ctx.postW, ne_of_gt hRpos, hΛzero]
  have hbadSub : ∀ Θ, ¬ D.Gate1 Θ g → D.R'.w (Θ g) < d := by
    intro Θ hnot
    by_contra hge
    exact hnot (hGateFromDen Θ (le_of_not_gt hge))
  calc
    D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) ≤
        D.rawHidden.pr (fun Θ => D.R'.w (Θ g) < d) :=
      FinProb.pr_mono D.rawHidden _ _ hbadSub
    _ ≤ Real.exp (-((D.n : ℝ) ^ (tau8 η₀ / 2))) := hSmallProb

/-- One filtering step (08:99): if a first-side law on `X` has width at most `n^η` and a second-side law on `Y` has
width at most `n^β`, the second law puts mass at most `2e^{-n^η}` on labels whose hit fraction into the first law
is outside `1/2 ± 2n^{-η}`. -/
def FilterStep (η₀ β : ℝ) (n : ℕ) : Prop :=
  ∀ (N : ℕ) (E : Fin N → Fin N → Prop) (X Y : Finset (Fin N)) (G : Colour) (μ ν : Law N),
    DiscOne E X Y ((n : ℝ) ^ η₀) ((n : ℝ) ^ η₀) ((n : ℝ) ^ (-η₀)) →
    μ.SupportedIn X → μ.WidthLE ((n : ℝ) ^ eta8 η₀) → ν.SupportedIn Y → ν.WidthLE ((n : ℝ) ^ β) →
    (∑ y, ν.w y * if 2 * (n : ℝ) ^ (-eta8 η₀) < |colDeg E G μ y - 1 / 2| then 1 else 0) ≤
      2 * Real.exp (-(n : ℝ) ^ eta8 η₀)

/-- L8.1c, filtering step (08:99): restricting `ν` to either exceptional set, if that set had `ν`-mass at least
`e^{-n^η}`, would give a law of width at most `n^β + n^η ≤ n^{η₀}` whose density with `μ` differs from `1/2` by
more than `2n^{-η} ≥ n^{-η₀}`, contradicting (7.2). -/
theorem filter_step (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, FilterStep η₀ β n := by
  have hη : 0 < eta8 η₀ := eta8_pos hη₀
  have hηhalf : eta8 η₀ ≤ η₀ / 2 := by
    unfold eta8
    exact min_le_left _ _
  have hgap : 0 < η₀ - eta8 η₀ := by linarith
  have hβη : β ≤ eta8 η₀ := by
    rw [tau8_eq] at hβτ
    linarith
  have hpowLarge : ∀ᶠ n : ℕ in Filter.atTop, 2 < (n : ℝ) ^ (η₀ - eta8 η₀) := by
    have ht := (_root_.tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (Filter.eventually_gt_atTop 2)] with n hn
    exact hn
  have hnLarge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n :=
    Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hnLarge.and hpowLarge)
  refine ⟨n₀, ?_⟩
  intro n hn
  have hlarge := hn₀ n hn
  have hn2 : 2 ≤ n := hlarge.1
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hpowη : (n : ℝ) ^ eta8 η₀ ≤ (n : ℝ) ^ η₀ :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hηhalf])
  have hpowβ : (n : ℝ) ^ β ≤ (n : ℝ) ^ eta8 η₀ :=
    Real.rpow_le_rpow_of_exponent_le hnR hβη
  have hpowId : (n : ℝ) ^ η₀ =
      (n : ℝ) ^ eta8 η₀ * (n : ℝ) ^ (η₀ - eta8 η₀) := by
    calc
      (n : ℝ) ^ η₀ = (n : ℝ) ^ (eta8 η₀ + (η₀ - eta8 η₀)) := by congr 1 <;> ring
      _ = (n : ℝ) ^ eta8 η₀ * (n : ℝ) ^ (η₀ - eta8 η₀) :=
        Real.rpow_add hnPos _ _
  have hpowTwice : 2 * (n : ℝ) ^ eta8 η₀ ≤ (n : ℝ) ^ η₀ := by
    calc
      2 * (n : ℝ) ^ eta8 η₀ ≤ (n : ℝ) ^ (η₀ - eta8 η₀) * (n : ℝ) ^ eta8 η₀ :=
        mul_le_mul_of_nonneg_right (le_of_lt hlarge.2)
          (Real.rpow_nonneg hnPos.le _)
      _ = (n : ℝ) ^ η₀ := by rw [hpowId]; ring
  have hpowWidth : (n : ℝ) ^ β + (n : ℝ) ^ eta8 η₀ ≤ (n : ℝ) ^ η₀ := by
    nlinarith [hpowβ, hpowTwice]
  have herr : (n : ℝ) ^ (-η₀) ≤ (n : ℝ) ^ (-eta8 η₀) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hηhalf])
  refine fun N E X Y G μ ν hdisc hμsupp hμwidth hνsupp hνwidth => ?_
  let eps : ℝ := (n : ℝ) ^ (-eta8 η₀)
  let small : ℝ := Real.exp (-((n : ℝ) ^ eta8 η₀))
  let plus : Finset (Fin N) := Finset.univ.filter fun y =>
    2 * eps < colDeg E G μ y - 1 / 2
  let minus : Finset (Fin N) := Finset.univ.filter fun y =>
    colDeg E G μ y - 1 / 2 < -(2 * eps)
  let massPlus : ℝ := ∑ y ∈ plus, ν.w y
  let massMinus : ℝ := ∑ y ∈ minus, ν.w y
  have heps : 0 < eps := Real.rpow_pos_of_pos hnPos _
  have hsmall : 0 < small := Real.exp_pos _
  have sideBound (S : Finset (Fin N)) (sgn : ℝ)
      (hsgn : sgn = 1 ∨ sgn = -1)
      (hside : ∀ y ∈ S, 2 * eps < sgn * (colDeg E G μ y - 1 / 2)) :
      (∑ y ∈ S, ν.w y) ≤ small := by
    by_contra hnot
    have hmass : small < ∑ y ∈ S, ν.w y := lt_of_not_ge hnot
    have hm : 0 < ∑ y ∈ S, ν.w y := lt_trans hsmall hmass
    let νS : Law N := Law.restrict ν S hm
    have hlog : -((n : ℝ) ^ eta8 η₀) < Real.log (∑ y ∈ S, ν.w y) := by
      rw [Real.lt_log_iff_exp_lt hm]
      simpa [small] using hmass
    have hνSWidth : νS.WidthLE ((n : ℝ) ^ η₀) := by
      apply Law.WidthLE.mono (Law.WidthLE.restrict hνwidth hm)
      calc
        (n : ℝ) ^ β - Real.log (∑ y ∈ S, ν.w y) ≤
            (n : ℝ) ^ β + (n : ℝ) ^ eta8 η₀ := by linarith
        _ ≤ (n : ℝ) ^ η₀ := hpowWidth
    have hνSSupp : νS.SupportedIn Y := by
      intro y hy
      by_cases hyS : y ∈ S
      · simp [νS, Law.restrict, hyS, hνsupp y hy]
      · simp [νS, Law.restrict, hyS]
    have hμSWidth : μ.WidthLE ((n : ℝ) ^ η₀) := by
      exact Law.WidthLE.mono hμwidth hpowη
    have hdenEq : dens E G μ νS = ∑ y, νS.w y * colDeg E G μ y := by
      classical
      unfold dens colDeg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ x, μ.w x * νS.w y * if Hits E G x y then 1 else 0) =
            ∑ x, νS.w y * (μ.w x * if Hits E G x y then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = νS.w y * ∑ x, μ.w x * if Hits E G x y then 1 else 0 :=
          (Finset.mul_sum _ _ _).symm
    have hmean :
        ∑ y, νS.w y * (sgn * (colDeg E G μ y - 1 / 2)) =
          sgn * (dens E G μ νS - 1 / 2) := by
      calc
        _ = ∑ y, sgn * (νS.w y * (colDeg E G μ y - 1 / 2)) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = sgn * ∑ y, νS.w y * (colDeg E G μ y - 1 / 2) := by
          rw [← Finset.mul_sum]
        _ = sgn * ((∑ y, νS.w y * colDeg E G μ y) -
            (∑ y, νS.w y * (1 / 2))) := by
          congr 1
          calc
            _ = ∑ y, (νS.w y * colDeg E G μ y - νS.w y * (1 / 2)) := by
              apply Finset.sum_congr rfl
              intro y _
              ring
            _ = _ := by rw [Finset.sum_sub_distrib]
        _ = sgn * (dens E G μ νS - 1 / 2) := by
          have hhalf : (∑ y, νS.w y * (1 / 2 : ℝ)) = 1 / 2 := by
            simpa [FinProb.expect] using FinProb.expect_const νS (1 / 2 : ℝ)
          rw [hdenEq, hhalf]
    have hposWeight : ∃ y, 0 < νS.w y := by
      by_contra hnone
      push_neg at hnone
      have hzero : ∀ y, νS.w y = 0 := by
        intro y
        exact le_antisymm (hnone y) (νS.nonneg y)
      have hsum : (∑ y, νS.w y) = 0 := by simp [hzero]
      rw [νS.sum_eq_one] at hsum
      norm_num at hsum
    have hmeanStrict : 2 * eps <
        ∑ y, νS.w y * (sgn * (colDeg E G μ y - 1 / 2)) := by
      obtain ⟨y₀, hy₀⟩ := hposWeight
      have hy₀S : y₀ ∈ S := by
        by_contra hy
        have : νS.w y₀ = 0 := by simp [νS, Law.restrict, hy]
        linarith
      have hsumLt :
          (∑ y, νS.w y) * (2 * eps) <
            ∑ y, νS.w y * (sgn * (colDeg E G μ y - 1 / 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_lt_sum
        · intro y _
          by_cases hy : y ∈ S
          · exact mul_le_mul_of_nonneg_left (le_of_lt (hside y hy)) (νS.nonneg y)
          · have hz : νS.w y = 0 := by simp [νS, Law.restrict, hy]
            simp [hz]
        · exact ⟨y₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hside y₀ hy₀S) hy₀⟩
      simpa [νS.sum_eq_one] using hsumLt
    have hdiscS := hdisc μ νS hμsupp hνSSupp hμSWidth hνSWidth G
    have habs := (abs_le.mp hdiscS)
    rcases hsgn with hsgn | hsgn
    · subst sgn
      rw [hmean] at hmeanStrict
      linarith [habs.2, herr]
    · subst sgn
      rw [hmean] at hmeanStrict
      linarith [habs.1, herr]
  have hplusSide : ∀ y ∈ plus, 2 * eps < 1 * (colDeg E G μ y - 1 / 2) := by
    intro y hy
    change y ∈ Finset.univ.filter (fun z => 2 * eps < colDeg E G μ z - 1 / 2) at hy
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, one_mul] using hy
  have hminusSide : ∀ y ∈ minus, 2 * eps < (-1) * (colDeg E G μ y - 1 / 2) := by
    intro y hy
    change y ∈ Finset.univ.filter (fun z => colDeg E G μ z - 1 / 2 < -(2 * eps)) at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    linarith
  have hplus : massPlus ≤ small := by
    dsimp [massPlus]
    exact sideBound plus 1 (Or.inl rfl) hplusSide
  have hminus : massMinus ≤ small := by
    dsimp [massMinus]
    exact sideBound minus (-1) (Or.inr rfl) hminusSide
  have hbadSubset : ∀ y, 2 * eps < |colDeg E G μ y - 1 / 2| →
      y ∈ plus ∨ y ∈ minus := by
    intro y hy
    by_cases hp : 2 * eps < colDeg E G μ y - 1 / 2
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
    · by_cases hm : colDeg E G μ y - 1 / 2 < -(2 * eps)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩)
      · apply False.elim
        exact (not_lt_of_ge (abs_le.mpr ⟨le_of_not_gt hm, le_of_not_gt hp⟩)) hy
  have htargetEq :
      (∑ y, ν.w y * if 2 * eps < |colDeg E G μ y - 1 / 2| then 1 else 0) =
        ν.pr (fun y => 2 * eps < |colDeg E G μ y - 1 / 2|) := by
    unfold FinProb.pr
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  have hbadmass :
      (∑ y, ν.w y * if 2 * eps < |colDeg E G μ y - 1 / 2| then 1 else 0) ≤
        massPlus + massMinus := by
    rw [htargetEq]
    calc
      ν.pr (fun y => 2 * eps < |colDeg E G μ y - 1 / 2|) ≤
          ν.pr (fun y => y ∈ plus ∨ y ∈ minus) :=
        FinProb.pr_mono ν _ _ hbadSubset
      _ ≤ ν.pr (fun y => y ∈ plus) + ν.pr (fun y => y ∈ minus) :=
        FinProb.pr_union ν _ _
      _ = massPlus + massMinus := by
        have hp : ν.pr (fun y => y ∈ plus) = massPlus := by
          classical
          unfold FinProb.pr
          dsimp
          trans (∑ y, if y ∈ plus then ν.w y else 0)
          · apply Finset.sum_congr rfl
            intro y _
            by_cases hy : y ∈ plus <;> simp [hy]
          · rw [Finset.sum_ite_mem_eq]
        have hm : ν.pr (fun y => y ∈ minus) = massMinus := by
          classical
          unfold FinProb.pr
          dsimp
          trans (∑ y, if y ∈ minus then ν.w y else 0)
          · apply Finset.sum_congr rfl
            intro y _
            by_cases hy : y ∈ minus <;> simp [hy]
          · rw [Finset.sum_ite_mem_eq]
        rw [hp, hm]
  calc
    _ = ∑ y, ν.w y * if 2 * eps < |colDeg E G μ y - 1 / 2| then 1 else 0 := by
      simp [eps]
    _ ≤ massPlus + massMinus := hbadmass
    _ ≤ 2 * small := by linarith [hplus, hminus]

/-- L8.1c(G3–G4) (08:90–105): filter the aggregates `μ̄_η = ∫ μ_i dη_g` (on (G1), `N max μ̄_η ≤ 4K e^{hn^β +
n^{τ/2}}`) and `μ̄_Λ` (`N max ≤ 4K`) successively by the coordinates of the independent cross tuples.  Given a cross
tuple's latent tag its coordinates are independent with law `ν_i`; after at most `2hs` regular hits the filtered
aggregate still has width below `n^η`, so by `FilterStep` a next hit fraction outside `1/2 ± 2n^{-η}` has
probability at most `2e^{-n^η}`.  The products of fractions over `h|E(g)| ≤ 2hs` coordinates are
`A_g(1 + o(1))`, and with one key omitted `2^h A_g(1 + o(1))`; the union costs `O(hs²) e^{-n^η}`. -/
theorem gate34_tail (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) (hK : 0 < K) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → FilterStep η₀ β D.n →
      ∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ≤
        Real.exp (-(D.n : ℝ) ^ (eta8 η₀ / 2)) := by
  obtain ⟨nF, hF⟩ := filter_step η₀ β hη₀ hβ₀ hβτ
  refine ⟨nF, ?_⟩
  intro D hn X Y R hStd hGrid hFilter g
  have hCrossCard := hGrid.crossKeys_card g
  have hStep : FilterStep η₀ β D.n := hFilter
  sorry

/-- L8.1c(G2) (08:107–123): with `L_g = ∫ (d_i^- - d_i^+) dη_g`, the own-colour defect `2ε` and survival
`α_x^{|E(g)|} ≤ 1.1A_g` give `E[L_g | Θ_g] ≤ 2.2hεA_g`; Markov at `.1ΔA_g` fails with probability
`O(hε/Δ) = exp(-n^p + n^{p/2} + O_h(1))`.  On (G3), the cutoff `d^+ ≥ (1-Δ)d^-` removes at most `L_g/Δ ≤ .1A_g`,
the cutoff `d^- ≥ e^{-n^{2τ}}` removes at most `e^{-n^{2τ}} = o(A_g)` (`log A_g^{-1} = O(hs)`), so
`.8A_g ≤ Z_g ≤ 1.2A_g`. -/
theorem gate2_tail (hη₀ : 0 < η₀) (hp : 0 < p) (hK : 0 < K) :
    ∃ c > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      ∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) ≤
        Real.exp (-(D.n : ℝ) ^ c) := by
  have cutoffLoss (D : Ctx η₀ β p h) (Θ : D.Hist) (g : D.KeyT)
      (h34 : D.Gate34 Θ g) (hnot : ¬ D.Gate2 Θ g)
      (hpost : ∑ i, D.postW (Θ g) i = 1)
      (hcut : D.cut ≤ (1 / 20 : ℝ) * D.AG g)
      (hΔpos : 0 < D.Δ) (hΔle : D.Δ ≤ 1) :
      (1 / 20 : ℝ) * D.Δ * D.AG g <
        ∑ i, D.postW (Θ g) i * (D.dMinus Θ g i - D.dPlus Θ g i) := by
    have hApos : 0 < D.AG g := by
      unfold Ctx.AG
      positivity
    have hpostNonneg (i : D.M.ι) : 0 ≤ D.postW (Θ g) i := D.postW_nonneg _ _
    have hdiffNonneg (i : D.M.ι) : 0 ≤ D.dMinus Θ g i - D.dPlus Θ g i := by
      have hdp : D.dPlus Θ g i ≤ D.dMinus Θ g i := by
        unfold Ctx.dPlus Ctx.dMinus
        apply Finset.sum_le_sum
        intro x _
        have hInd : (if D.ownHit Θ g x then (1 : ℝ) else 0) ≤
            (if D.crossHit Θ g x then (1 : ℝ) else 0) := by
          by_cases hc : D.crossHit Θ g x
          · by_cases ho : D.hitsAll x (Θ g) <;> simp [Ctx.ownHit, hc, ho]
          · have ho : ¬ D.ownHit Θ g x := by
              intro hh
              exact hc hh.1
            simp [hc, ho]
        exact mul_le_mul_of_nonneg_left hInd ((D.M.μ i).nonneg x)
      linarith
    have htotalLo : D.AG g / (11 / 10 : ℝ) ≤
        ∑ i, D.postW (Θ g) i * D.dMinus Θ g i := h34.1.1
    have htotalHi :
        ∑ i, D.postW (Θ g) i * D.dMinus Θ g i ≤ (11 / 10 : ℝ) * D.AG g := h34.1.2
    have hZleTotal : D.ZG Θ g ≤ ∑ i, D.postW (Θ g) i * D.dMinus Θ g i := by
      unfold Ctx.ZG
      apply Finset.sum_le_sum
      intro i _
      by_cases hopen : D.GateOpen Θ g i
      · simp [Ctx.tiltW, hopen]
      · simp [Ctx.tiltW, hopen]
        exact mul_nonneg (hpostNonneg i) (D.dMinus_nonneg Θ g i)
    have hZupper : D.ZG Θ g ≤ (12 / 10 : ℝ) * D.AG g := by
      calc
        D.ZG Θ g ≤ ∑ i, D.postW (Θ g) i * D.dMinus Θ g i := hZleTotal
        _ ≤ (11 / 10 : ℝ) * D.AG g := htotalHi
        _ ≤ (12 / 10 : ℝ) * D.AG g := by nlinarith [hApos]
    have hZsmall : D.ZG Θ g < (8 / 10 : ℝ) * D.AG g := by
      by_contra hz
      apply hnot
      exact ⟨le_of_not_gt hz, hZupper⟩
    let L : ℝ := ∑ i, D.postW (Θ g) i * (D.dMinus Θ g i - D.dPlus Θ g i)
    have hremoved (i : D.M.ι) :
        D.postW (Θ g) i * D.dMinus Θ g i ≤
          D.tiltW Θ g i + D.postW (Θ g) i * D.cut +
            D.postW (Θ g) i * (D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ := by
      by_cases hopen : D.GateOpen Θ g i
      · simp [Ctx.tiltW, hopen]
        have hcutterm : 0 ≤ D.postW (Θ g) i * D.cut :=
          mul_nonneg (hpostNonneg i) (Real.exp_nonneg _)
        have hlast : 0 ≤ D.postW (Θ g) i *
            (D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ :=
          div_nonneg (mul_nonneg (hpostNonneg i) (hdiffNonneg i)) hΔpos.le
        linarith [hcutterm, hlast]
      · by_cases hlow : D.cut ≤ D.dMinus Θ g i
        · have hratio : ¬ ((1 - D.Δ) * D.dMinus Θ g i ≤ D.dPlus Θ g i) := by
            intro hratio
            exact hopen ⟨hlow, hratio⟩
          have hratio' : D.dPlus Θ g i < (1 - D.Δ) * D.dMinus Θ g i := lt_of_not_ge hratio
          have hgap : D.Δ * D.dMinus Θ g i ≤
              D.dMinus Θ g i - D.dPlus Θ g i := by nlinarith [hratio', D.dMinus_nonneg Θ g i]
          have hdiv : D.dMinus Θ g i ≤
              (D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ :=
            (le_div_iff₀ hΔpos).2 (by nlinarith [hgap])
          have hmul := mul_le_mul_of_nonneg_left hdiv (hpostNonneg i)
          have hmul' : D.postW (Θ g) i * D.dMinus Θ g i ≤
              D.postW (Θ g) i * (D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ := by
            calc
              _ ≤ D.postW (Θ g) i *
                  ((D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ) := hmul
              _ = _ := by ring
          simp [Ctx.tiltW, hopen]
          have hcutterm : 0 ≤ D.postW (Θ g) i * D.cut :=
            mul_nonneg (hpostNonneg i) (Real.exp_nonneg _)
          linarith [hmul', hcutterm]
        · have hlow' : D.dMinus Θ g i < D.cut := lt_of_not_ge hlow
          have hmul : D.postW (Θ g) i * D.dMinus Θ g i ≤
              D.postW (Θ g) i * D.cut :=
            mul_le_mul_of_nonneg_left hlow'.le (hpostNonneg i)
          simp [Ctx.tiltW, hopen]
          have hlast : 0 ≤ D.postW (Θ g) i *
              (D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ :=
            div_nonneg (mul_nonneg (hpostNonneg i) (hdiffNonneg i)) hΔpos.le
          linarith [hmul, hlast]
    have hsumRemoved :
        (∑ i, D.postW (Θ g) i * D.dMinus Θ g i) ≤ D.ZG Θ g + D.cut + L / D.Δ := by
      calc
        _ ≤ ∑ i, (D.tiltW Θ g i + D.postW (Θ g) i * D.cut +
            D.postW (Θ g) i * (D.dMinus Θ g i - D.dPlus Θ g i) / D.Δ) := by
          apply Finset.sum_le_sum
          intro i _
          exact hremoved i
        _ = D.ZG Θ g + D.cut * (∑ i, D.postW (Θ g) i) +
            (∑ i, D.postW (Θ g) i * (D.dMinus Θ g i - D.dPlus Θ g i)) / D.Δ := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_div]
          simp [Ctx.ZG]
          ring
        _ = D.ZG Θ g + D.cut + L / D.Δ := by simp [L, hpost]
    by_contra hL
    have hLle : L ≤ (1 / 20 : ℝ) * D.Δ * D.AG g := le_of_not_gt hL
    have hLdiv : L / D.Δ ≤ (1 / 20 : ℝ) * D.AG g := by
      rw [div_le_iff₀ hΔpos]
      nlinarith [hLle]
    have htotalBound :
        ∑ i, D.postW (Θ g) i * D.dMinus Θ g i <
          (9 / 10 : ℝ) * D.AG g := by
      have hsum := hsumRemoved
      have hcut' := hcut
      have hZ := hZsmall
      have hL' := hLdiv
      linarith
    have hbad : (D.AG g / (11 / 10 : ℝ)) < (9 / 10 : ℝ) * D.AG g :=
      lt_of_le_of_lt htotalLo htotalBound
    have hApos' := hApos
    norm_num at hbad
    nlinarith [hApos']
  sorry

/-- L8.1c, union bound (08:76): three stretched-exponential tails at exponents `a, b, c` give a base-gate tail at
exponent `min(a, b, c)/2` for large `n`. -/
theorem gate_tail_of (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n →
      (∀ g, D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) ≤ Real.exp (-(D.n : ℝ) ^ a)) →
      (∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ≤ Real.exp (-(D.n : ℝ) ^ b)) →
      (∀ g, D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) ≤
        Real.exp (-(D.n : ℝ) ^ c)) →
      D.GateTail (min (min a b) c / 2) := by
  set d := min (min a b) c with hd
  have hdpos : 0 < d := by
    dsimp [d]
    exact lt_min (lt_min ha hb) hc
  have hda : d ≤ a := by dsimp [d]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hdb : d ≤ b := by dsimp [d]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdc : d ≤ c := by dsimp [d]; exact min_le_right _ _
  have hdhalf : 0 < d / 2 := by positivity
  have hpow : ∀ᶠ n : ℕ in Filter.atTop, 4 < (n : ℝ) ^ (d / 2) := by
    have ht := (_root_.tendsto_rpow_atTop hdhalf).comp tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (Filter.eventually_gt_atTop 4)] with n hn
    exact hn
  have hnge : ∀ᶠ n : ℕ in Filter.atTop, 2 ≤ n := Filter.eventually_atTop.2 ⟨2, fun _ hn => hn⟩
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 (hnge.and hpow)
  refine ⟨n₀, ?_⟩
  intro D hn h1 h2 h3 g
  have hthreshold := hn₀ D.n hn
  have hn2 : 2 ≤ D.n := hthreshold.1
  have hnR : 1 < (D.n : ℝ) := by exact_mod_cast (by omega : 1 < D.n)
  have hx : 4 < (D.n : ℝ) ^ (d / 2) := hthreshold.2
  have hpowA : (D.n : ℝ) ^ d ≤ (D.n : ℝ) ^ a :=
    Real.rpow_le_rpow_of_exponent_le hnR.le hda
  have hpowB : (D.n : ℝ) ^ d ≤ (D.n : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hnR.le hdb
  have hpowC : (D.n : ℝ) ^ d ≤ (D.n : ℝ) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hnR.le hdc
  have hexpA : Real.exp (-((D.n : ℝ) ^ a)) ≤ Real.exp (-((D.n : ℝ) ^ d)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpB : Real.exp (-((D.n : ℝ) ^ b)) ≤ Real.exp (-((D.n : ℝ) ^ d)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hexpC : Real.exp (-((D.n : ℝ) ^ c)) ≤ Real.exp (-((D.n : ℝ) ^ d)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbad : ∀ Θ, ¬ D.BaseGates Θ g →
      (¬ D.Gate1 Θ g) ∨ (D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ∨
        (D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) := by
    intro Θ hbad
    by_cases hG1 : D.Gate1 Θ g
    · by_cases hG34 : D.Gate34 Θ g
      · right; right
        refine ⟨hG1, hG34, ?_⟩
        intro hG2
        exact hbad ⟨hG1, hG2, hG34⟩
      · exact Or.inr (Or.inl ⟨hG1, hG34⟩)
    · exact Or.inl hG1
  have hprob : D.rawHidden.pr (fun Θ => ¬ D.BaseGates Θ g) ≤
      D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) +
        D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) +
        D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) := by
    calc
      _ ≤ D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g ∨
          (D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ∨
            (D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g)) := by
        apply HypercubeRamsey.FinProb.pr_mono
        exact hbad
      _ ≤ D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) +
          D.rawHidden.pr (fun Θ => (D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) ∨
            (D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g)) :=
        HypercubeRamsey.FinProb.pr_union _ _ _
      _ ≤ D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) +
          (D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) +
            D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g)) := by
        have hbcu := HypercubeRamsey.FinProb.pr_union D.rawHidden
          (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g)
          (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g)
        linarith
      _ = (D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) +
          D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g)) +
            D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) := by ring
  have htail : D.rawHidden.pr (fun Θ => ¬ D.BaseGates Θ g) ≤
      3 * Real.exp (-((D.n : ℝ) ^ d)) := by
    calc
      _ ≤ D.rawHidden.pr (fun Θ => ¬ D.Gate1 Θ g) +
          D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ ¬ D.Gate34 Θ g) +
          D.rawHidden.pr (fun Θ => D.Gate1 Θ g ∧ D.Gate34 Θ g ∧ ¬ D.Gate2 Θ g) := hprob
      _ ≤ Real.exp (-((D.n : ℝ) ^ a)) + Real.exp (-((D.n : ℝ) ^ b)) +
          Real.exp (-((D.n : ℝ) ^ c)) := by
        linarith [h1 g, h2 g, h3 g]
      _ ≤ 3 * Real.exp (-((D.n : ℝ) ^ d)) := by
        nlinarith [hexpA, hexpB, hexpC, Real.exp_pos (-((D.n : ℝ) ^ d))]
  have hpow_id : (D.n : ℝ) ^ d =
      (D.n : ℝ) ^ (d / 2) * (D.n : ℝ) ^ (d / 2) := by
    calc
      (D.n : ℝ) ^ d = (D.n : ℝ) ^ (d / 2 + d / 2) := by congr 1 <;> ring
      _ = (D.n : ℝ) ^ (d / 2) * (D.n : ℝ) ^ (d / 2) :=
        Real.rpow_add (by positivity : 0 < (D.n : ℝ)) _ _
  have hxpos : 0 < (D.n : ℝ) ^ (d / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hgap : (D.n : ℝ) ^ (d / 2) ≤
      (D.n : ℝ) ^ d - 2 := by
    rw [hpow_id]
    nlinarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hfinal : 3 * Real.exp (-((D.n : ℝ) ^ d)) ≤
      Real.exp (-((D.n : ℝ) ^ (d / 2))) := by
    rw [show (3 : ℝ) = Real.exp (Real.log 3) by rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hpow_id]
    nlinarith
  exact le_trans htail hfinal

/-- L8.1c assembled (08:76–123): for some `c' > 0`, the raw probability that a base gate fails at a key is at most
`e^{-n^{c'}}` for large `n`. -/
theorem gate_tail (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) (hp : 0 < p) (hK : 0 < K) :
    ∃ c' > (0 : ℝ), ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N),
      Std D γ K X Y R → GridFacts η₀ D.n → D.GateTail c' := by
  obtain ⟨nF, hF⟩ := filter_step η₀ β hη₀ hβ₀ hβτ
  obtain ⟨n₁', h34⟩ := gate34_tail η₀ γ β p K h hη₀ hβ₀ hβτ hK
  obtain ⟨c, hc, n₂, h2⟩ := gate2_tail η₀ γ β p K h hη₀ hp hK
  obtain ⟨n₃, hU⟩ := gate_tail_of η₀ β p h (tau8 η₀ / 2) (eta8 η₀ / 2) c
    (by linarith [tau8_pos hη₀]) (by linarith [eta8_pos hη₀]) hc
  set n₁ := max nF n₁' with hn₁def
  refine ⟨min (min (tau8 η₀ / 2) (eta8 η₀ / 2)) c / 2, ?_, max (max n₁ n₂) n₃, ?_⟩
  · have h1 : 0 < tau8 η₀ / 2 := by linarith [tau8_pos hη₀]
    have h2' : 0 < eta8 η₀ / 2 := by linarith [eta8_pos hη₀]
    have : 0 < min (min (tau8 η₀ / 2) (eta8 η₀ / 2)) c := lt_min (lt_min h1 h2') hc
    linarith
  · intro D hn X Y R hS hG
    have hn₁ : n₁ ≤ D.n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnF : nF ≤ D.n := le_trans (le_max_left _ _) hn₁
    have hn₁' : n₁' ≤ D.n := le_trans (le_max_right _ _) hn₁
    have hn₂ : n₂ ≤ D.n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn₃ : n₃ ≤ D.n := le_trans (le_max_right _ _) hn
    exact hU D hn₃ (gate1_tail η₀ γ β p K h hη₀ hβ₀ D X Y R hS)
      (h34 D hn₁' X Y R hS hG (hF D.n hnF)) (h2 D hn₂ X Y R hS)

/-! ## L8.1e: the fixed-presentation reference experiment (08:139–176) -/

/-- L8.1e(i) (08:144–154): on the candidate's gates, `S_g ≤ e^{hn^β + n^{τ/2}} Λ d^- / (.8A_g)` (G1, G2) and the
internal reference is `Λ d^- / ∫d^- dΛ` with `∫ d^- dΛ ≤ 1.1A_g` (G3), giving density `≤ e^{hn^β + n^{τ/2} + 1}`;
at `u ∈ E(g)`, `S_u(i)U_{u,i}(x) ≤ η_u(i)μ_i(x)1[x hits Θ_w, w ∈ E(u) ∪ {u}]/((1-Δ)Z_u)` since
`d_i^- / d_i^+ ≤ (1-Δ)^{-1}`, and the cross normalizer is at most `1.1 · 2^h A_u` (G4 at `u` omitting `g`), giving
density `≤ 2^{h+2}` (`Δ ≤ e^{-1}` for `n ≥ 1`). -/
theorem density_bounds (hp : 0 < p) (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) : D.DensityBounds := by
  intro Θ g ξ hCand
  let H : D.Hist := Function.update Θ g ξ
  have hgNot : g ∉ crossKeys g := by
    have hdiag : keyDist g g = 0 := by
      unfold keyDist
      simp
    unfold crossKeys
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdiag]
    norm_num
  have hCrossHitEq (x : Fin D.N) : D.crossHit H g x = D.crossHit Θ g x := by
    apply propext
    constructor
    · intro hhit u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        exact hgNot hu
      have hval : H u = Θ u := by simp [H, hne]
      simpa [hval] using hhit u hu
    · intro hhit u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        exact hgNot hu
      have hval : H u = Θ u := by simp [H, hne]
      simpa [hval] using hhit u hu
  have hDMinusEq (i : D.M.ι) : D.dMinus H g i = D.dMinus Θ g i := by
    simp [Ctx.dMinus, hCrossHitEq]
  have hAG (u : D.KeyT) : 0 < D.AG u := by
    unfold Ctx.AG
    positivity
  have hGate1 := hCand.1.1
  rcases hCand.1.2 with ⟨hGate2, hGate34⟩
  rcases hGate2 with ⟨hZlower, hZupper⟩
  rcases hGate34 with ⟨hEtaG3, hGate34rest⟩
  rcases hGate34rest with ⟨hLambdaG3, hGate4⟩
  have hZpos : 0 < D.ZG H g := lt_of_lt_of_le
    (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) (hAG g)) hZlower
  let L : ℝ := ∑ i, D.M.Λ i * D.dMinus Θ g i
  have hLambdaEq : (∑ i, D.M.Λ i * D.dMinus H g i) = L := by
    change (∑ i, D.M.Λ i * D.dMinus H g i) =
      ∑ i, D.M.Λ i * D.dMinus Θ g i
    apply Finset.sum_congr rfl
    intro i _
    rw [hDMinusEq]
  have hLupper : L ≤ (11 / 10 : ℝ) * D.AG g := by
    have h := hLambdaG3.2
    rw [hLambdaEq] at h
    exact h
  have hLlower : D.AG g / (11 / 10 : ℝ) ≤ L := by
    have h := hLambdaG3.1
    rw [hLambdaEq] at h
    exact h
  have hLpos : 0 < L := lt_of_lt_of_le
    (div_pos (hAG g) (by norm_num)) hLlower
  have hLnorm : L ≤ Real.exp 1 * D.ZG H g := by
    have he : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    calc
      L ≤ (11 / 10 : ℝ) * D.AG g := hLupper
      _ ≤ Real.exp 1 * ((8 / 10 : ℝ) * D.AG g) := by nlinarith [hAG g, he]
      _ ≤ Real.exp 1 * D.ZG H g :=
        mul_le_mul_of_nonneg_left hZlower (Real.exp_nonneg 1)
  have hNormTilt (i : D.M.ι) :
      (D.tilt H g).w i = D.tiltW H g i / D.ZG H g := by
    have hsum : (∑ i', D.tiltW H g i') ≠ 0 := by
      intro hz
      apply (ne_of_gt hZpos)
      simpa [Ctx.ZG] using hz
    simp [Ctx.tilt, HypercubeRamsey.S08.normOr, Ctx.ZG, hsum]
  have hNormRef (i : D.M.ι) :
      (D.refInt Θ g).w i =
        (D.M.Λ i * D.dMinus Θ g i) / L := by
    simp [Ctx.refInt, HypercubeRamsey.S08.normOr, L, ne_of_gt hLpos]
  have hOpenOfTilt (u : D.KeyT) (i : D.M.ι) (hBase : D.BaseGates H u)
      (hTilt : (D.tilt H u).w i ≠ 0) : D.GateOpen H u i := by
    have hAGu : 0 < D.AG u := hAG u
    have hZu : 0 < D.ZG H u :=
      lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) hAGu) hBase.2.1.1
    have hsum : (∑ i', D.tiltW H u i') ≠ 0 := by
      intro hz
      apply (ne_of_gt hZu)
      simpa [Ctx.ZG] using hz
    have hformula : (D.tilt H u).w i = D.tiltW H u i / D.ZG H u := by
      simp [Ctx.tilt, HypercubeRamsey.S08.normOr, Ctx.ZG, hsum]
    have hweight : D.tiltW H u i ≠ 0 := by
      intro hz
      apply hTilt
      rw [hformula, hz]
      simp
    by_contra hnot
    apply hweight
    simp [Ctx.tiltW, hnot]
  have hExp1 : 0 < Real.exp 1 := Real.exp_pos _
  constructor
  · intro i
    by_cases hopen : D.GateOpen H g i
    · have hdm : 0 ≤ D.dMinus H g i := D.dMinus_nonneg H g i
      have htop : D.postW (H g) i * D.dMinus H g i ≤
          Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
            (D.M.Λ i * D.dMinus H g i) := by
        calc
          _ = (D.postW (H g) i * D.dMinus H g i) := rfl
          _ ≤ (Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) * D.M.Λ i) *
              D.dMinus H g i :=
            mul_le_mul_of_nonneg_right (hGate1 i) hdm
          _ = _ := by ring
      have htopΘ : D.postW (H g) i * D.dMinus Θ g i ≤
          Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
            (D.M.Λ i * D.dMinus Θ g i) := by
        simpa [hDMinusEq] using htop
      have hTiltBound : (D.tilt H g).w i ≤
          Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
            (D.M.Λ i * D.dMinus Θ g i) / D.ZG H g := by
        rw [hNormTilt]
        unfold Ctx.tiltW
        simp [hopen]
        rw [hDMinusEq]
        exact div_le_div_of_nonneg_right htopΘ hZpos.le
      have hA : 0 ≤ D.M.Λ i * D.dMinus Θ g i :=
        mul_nonneg (D.M.Λ_nonneg i) (D.dMinus_nonneg Θ g i)
      have hscale : (D.M.Λ i * D.dMinus Θ g i) / D.ZG H g ≤
          Real.exp 1 * (D.M.Λ i * D.dMinus Θ g i) / L := by
        apply (div_le_div_iff₀ hZpos hLpos).2
        calc
          (D.M.Λ i * D.dMinus Θ g i) * L ≤
              (D.M.Λ i * D.dMinus Θ g i) * (Real.exp 1 * D.ZG H g) :=
            mul_le_mul_of_nonneg_left hLnorm hA
          _ = Real.exp 1 * (D.M.Λ i * D.dMinus Θ g i) * D.ZG H g := by ring
      calc
        (D.tilt H g).w i ≤
            Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
              ((D.M.Λ i * D.dMinus Θ g i) / D.ZG H g) := by
          simpa [div_eq_mul_inv, mul_assoc] using hTiltBound
        _ ≤ Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
            (Real.exp 1 * (D.M.Λ i * D.dMinus Θ g i) / L) :=
          mul_le_mul_of_nonneg_left hscale (Real.exp_nonneg _)
        _ = Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) *
            (D.refInt Θ g).w i := by
          have hE : Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
              Real.exp 1 = Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) := by
            rw [← Real.exp_add]
          rw [hNormRef]
          calc
            _ = (Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2)) *
                Real.exp 1) * (D.M.Λ i * D.dMinus Θ g i / L) := by ring
            _ = _ := by rw [hE]
    · rw [hNormTilt]
      have hzero : D.tiltW H g i = 0 := by
        unfold Ctx.tiltW
        simp [hopen]
      rw [hzero]
      simp only [zero_div]
      exact mul_nonneg (Real.exp_nonneg _) ((D.refInt Θ g).nonneg i)
  · have hKeyDistSymm (u v : D.KeyT) : keyDist u v = keyDist v u := by
      unfold keyDist
      apply Finset.sum_congr rfl
      intro r _
      exact Nat.dist_comm _ _
    have hCrossSymm (u : D.KeyT) (hu : u ∈ crossKeys g) : g ∈ crossKeys u := by
      have hu' : keyDist g u = 1 := by simpa [crossKeys] using hu
      have hg' : keyDist u g = 1 := by rw [hKeyDistSymm]; exact hu'
      simpa [crossKeys] using hg'
    have hnR : 0 < (D.n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
    have hnR1 : 1 ≤ (D.n : ℝ) := by exact_mod_cast hn
    have hp2 : 0 ≤ p / 2 := by linarith
    have hpowAtLeastOne : 1 ≤ (D.n : ℝ) ^ (p / 2) := by
      calc
        1 = (D.n : ℝ) ^ (0 : ℝ) := by simp
        _ ≤ (D.n : ℝ) ^ (p / 2) :=
          Real.rpow_le_rpow_of_exponent_le hnR1 hp2
    have hExpNegOne : Real.exp (-1) < 1 / 2 := by
      rw [Real.exp_neg]
      simpa [one_div] using
        (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two)
    have hDeltaHalf : D.Δ < 1 / 2 := by
      unfold Ctx.Δ
      exact (Real.exp_le_exp.mpr (by linarith [hpowAtLeastOne])).trans_lt hExpNegOne
    have hCoef : 0 < 1 - D.Δ := by linarith
    have hCoefHalf : 1 / 2 ≤ 1 - D.Δ := by linarith
    intro u q
    have hUnG : u.1 ≠ g := by
      intro heq
      apply hgNot
      simpa [heq] using u.2
    have hHu : H u.1 = Θ u.1 := by simp [H, hUnG]
    have hOmitPredEq (x : Fin D.N) :
        (∀ w, w ≠ g ∧ w ∈ crossKeys u.1 → D.hitsAll x (H w)) =
          (∀ w, w ≠ g ∧ w ∈ crossKeys u.1 → D.hitsAll x (Θ w)) := by
      apply propext
      constructor
      · intro hh w hwm
        rcases hwm with ⟨hne, hmem⟩
        have hw : w ∈ (crossKeys u.1).erase g := Finset.mem_erase.mpr ⟨hne, hmem⟩
        have hval : H w = Θ w := by simp [H, hne]
        simpa [hval] using hh w ⟨hne, hmem⟩
      · intro hh w hwm
        rcases hwm with ⟨hne, hmem⟩
        have hw : w ∈ (crossKeys u.1).erase g := Finset.mem_erase.mpr ⟨hne, hmem⟩
        have hval : H w = Θ w := by simp [H, hne]
        simpa [hval] using hh w ⟨hne, hmem⟩
    have hOmitEq (i : D.M.ι) :
        D.dOmit H u.1 g i = D.dOmit Θ u.1 g i := by
      unfold Ctx.dOmit
      apply Finset.sum_congr rfl
      intro x _
      simp only [Finset.mem_erase]
      by_cases hh : ∀ w, w ≠ g ∧ w ∈ crossKeys u.1 → D.hitsAll x (H w)
      · have hh' := Eq.mp (hOmitPredEq x) hh
        rw [if_pos hh, if_pos hh']
      · have hh' : ¬ ∀ w, w ≠ g ∧ w ∈ crossKeys u.1 → D.hitsAll x (Θ w) := by
          intro h'
          exact hh (Eq.mpr (hOmitPredEq x) h')
        rw [if_neg hh, if_neg hh']
    have hOmitSum (i : D.M.ι) :
        (∑ x, (D.M.μ i).w x * if D.omitHit Θ u.1 g x then 1 else 0) =
          D.dOmit Θ u.1 g i := by
      unfold Ctx.dOmit Ctx.omitHit
      apply Finset.sum_congr rfl
      intro x _
      by_cases hh : ∀ w ∈ (crossKeys u.1).erase g, D.hitsAll x (Θ w) <;> simp [hh]
    have hPostEq (i : D.M.ι) : D.postW (H u.1) i = D.postW (Θ u.1) i := by
      rw [hHu]
    have hBaseU : D.BaseGates H u.1 := hCand.2 u.1 u.2
    rcases hBaseU with ⟨hGate1U, hGate2U, hGate34U⟩
    rcases hGate2U with ⟨hZUlower, hZUupper⟩
    rcases hGate34U with ⟨hEtaG3U, hGate34restU⟩
    rcases hGate34restU with ⟨hLambdaG3U, hGate4U⟩
    have hBaseU : D.BaseGates H u.1 :=
      ⟨hGate1U, ⟨hZUlower, hZUupper⟩, ⟨hEtaG3U, ⟨hLambdaG3U, hGate4U⟩⟩⟩
    have hZUpos : 0 < D.ZG H u.1 :=
      lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) (hAG u.1)) hZUlower
    have huG : g ∈ crossKeys u.1 := hCrossSymm u.1 u.2
    have hOmitGates := hGate4U g huG
    let Lx : ℝ := ∑ z : D.M.ι × Fin D.N,
      D.postW (Θ u.1) z.1 * (D.M.μ z.1).w z.2 *
        if D.omitHit Θ u.1 g z.2 then 1 else 0
    have hLxEq : Lx = ∑ i, D.postW (H u.1) i * D.dOmit H u.1 g i := by
      unfold Lx
      rw [Fintype.sum_prod_type]
      calc
        (∑ i, ∑ x, D.postW (Θ u.1) i * (D.M.μ i).w x *
            if D.omitHit Θ u.1 g x then 1 else 0) =
          ∑ i, D.postW (Θ u.1) i *
            ∑ x, (D.M.μ i).w x * if D.omitHit Θ u.1 g x then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          calc
            _ = ∑ x, D.postW (Θ u.1) i *
                ((D.M.μ i).w x * if D.omitHit Θ u.1 g x then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
            _ = D.postW (Θ u.1) i *
                ∑ x, (D.M.μ i).w x * if D.omitHit Θ u.1 g x then 1 else 0 := by
              rw [← Finset.mul_sum]
        _ = ∑ i, D.postW (H u.1) i * D.dOmit H u.1 g i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hPostEq i, hOmitEq i]
          rw [← hOmitSum i]
    have hLxUpper : Lx ≤ (11 / 10 : ℝ) * (2 : ℝ) ^ h * D.AG u.1 := by
      rw [hLxEq]
      exact hOmitGates.1.2
    have hLxLower : (2 : ℝ) ^ h * D.AG u.1 / (11 / 10 : ℝ) ≤ Lx := by
      rw [hLxEq]
      exact hOmitGates.1.1
    have hLxPos : 0 < Lx := lt_of_lt_of_le
      (div_pos (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) h) (hAG u.1))
        (by norm_num)) hLxLower
    have hNormRefCross (z : D.M.ι × Fin D.N) :
        (D.refCross Θ g u.1).w z =
          (D.postW (Θ u.1) z.1 * (D.M.μ z.1).w z.2 *
            if D.omitHit Θ u.1 g z.2 then 1 else 0) / Lx := by
      have hsumNe : (∑ z' : D.M.ι × Fin D.N,
          D.postW (Θ u.1) z'.1 * (D.M.μ z'.1).w z'.2 *
            if D.omitHit Θ u.1 g z'.2 then 1 else 0) ≠ 0 := by
        change Lx ≠ 0
        exact ne_of_gt hLxPos
      have hsumNe' : (∑ z' : D.M.ι × Fin D.N,
          if D.omitHit Θ u.1 g z'.2 then
            D.postW (Θ u.1) z'.1 * (D.M.μ z'.1).w z'.2 else 0) ≠ 0 := by
        simpa [mul_ite] using hsumNe
      simp [Ctx.refCross, HypercubeRamsey.S08.normOr, hsumNe', Lx]
    have hTiltNormU (i : D.M.ι) :
        (D.tilt H u.1).w i = D.tiltW H u.1 i / D.ZG H u.1 := by
      have hsum : (∑ i', D.tiltW H u.1 i') ≠ 0 := by
        intro hz
        apply (ne_of_gt hZUpos)
        simpa [Ctx.ZG] using hz
      simp [Ctx.tilt, HypercubeRamsey.S08.normOr, Ctx.ZG, hsum]
    have hDeltapow : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
    have hCut : 0 < D.cut := Real.exp_pos _
    by_cases hTiltZero : (D.tilt H u.1).w q.1 = 0
    · have hRnonneg : 0 ≤ (D.refCross Θ g u.1).w q := (D.refCross Θ g u.1).nonneg q
      calc
        (D.tilt H u.1).w q.1 * (D.anchorU H u.1 q.1).w q.2 = 0 := by
          rw [hTiltZero]
          simp
        _ ≤ (2 : ℝ) ^ (h + 2) * (D.refCross Θ g u.1).w q :=
          mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hRnonneg
    · have hOpen := hOpenOfTilt u.1 q.1 hBaseU hTiltZero
      have hDMinus : 0 < D.dMinus H u.1 q.1 := lt_of_lt_of_le hCut hOpen.1
      have hDPlus : 0 < D.dPlus H u.1 q.1 :=
        lt_of_lt_of_le (mul_pos hCoef hDMinus) hOpen.2
      have hsumPlus : (∑ x, if D.ownHit H u.1 x then (D.M.μ q.1).w x else 0) ≠ 0 := by
        simpa [Ctx.dPlus] using ne_of_gt hDPlus
      have hAnchorFormula : (D.anchorU H u.1 q.1).w q.2 =
          ((D.M.μ q.1).w q.2 * if D.ownHit H u.1 q.2 then 1 else 0) /
            D.dPlus H u.1 q.1 := by
        change (if (∑ x, (D.M.μ q.1).w x *
              if D.ownHit H u.1 x then 1 else 0) = 0 then
          (D.M.μ q.1).w q.2 else
          ((D.M.μ q.1).w q.2 * if D.ownHit H u.1 q.2 then 1 else 0) /
            (∑ x, (D.M.μ q.1).w x * if D.ownHit H u.1 x then 1 else 0)) =
          ((D.M.μ q.1).w q.2 * if D.ownHit H u.1 q.2 then 1 else 0) /
            D.dPlus H u.1 q.1
        rw [if_neg (by simpa using hsumPlus)]
        rfl
      have hOwnOmit : D.ownHit H u.1 q.2 → D.omitHit Θ u.1 g q.2 := by
        intro hOwn
        intro w hw
        have hHit := hOwn.1 w (Finset.mem_of_mem_erase hw)
        have hval : H w = Θ w := by
          simp [H, (Finset.mem_erase.mp hw).1]
        simpa [hval] using hHit
      have hNumBound :
          (D.tilt H u.1).w q.1 * (D.anchorU H u.1 q.1).w q.2 ≤
            (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
              if D.omitHit Θ u.1 g q.2 then 1 else 0) /
              (D.ZG H u.1 * (1 - D.Δ)) := by
        by_cases hOwn : D.ownHit H u.1 q.2
        · have hOmit := hOwnOmit hOwn
          have hUFormula : (D.anchorU H u.1 q.1).w q.2 =
              (D.M.μ q.1).w q.2 / D.dPlus H u.1 q.1 := by
            rw [hAnchorFormula]
            simp [hOwn]
          have hTiltFormula : (D.tilt H u.1).w q.1 =
              D.postW (H u.1) q.1 * D.dMinus H u.1 q.1 / D.ZG H u.1 := by
            rw [hTiltNormU]
            simp [Ctx.tiltW, hOpen]
          have hRatioCut : D.dMinus H u.1 q.1 / D.dPlus H u.1 q.1 ≤
              1 / (1 - D.Δ) := by
            apply (div_le_div_iff₀ hDPlus hCoef).2
            simpa [mul_comm] using hOpen.2
          have hApos : 0 ≤ D.postW (H u.1) q.1 * (D.M.μ q.1).w q.2 :=
            mul_nonneg (D.postW_nonneg _ _) ((D.M.μ q.1).nonneg _)
          calc
            _ = (D.postW (H u.1) q.1 * (D.M.μ q.1).w q.2 /
                  D.ZG H u.1) * (D.dMinus H u.1 q.1 / D.dPlus H u.1 q.1) := by
              rw [hTiltFormula, hUFormula]
              field_simp [ne_of_gt hZUpos, ne_of_gt hDPlus]
            _ ≤ (D.postW (H u.1) q.1 * (D.M.μ q.1).w q.2 /
                  D.ZG H u.1) * (1 / (1 - D.Δ)) :=
              mul_le_mul_of_nonneg_left hRatioCut
                (div_nonneg hApos hZUpos.le)
            _ = (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
                  if D.omitHit Θ u.1 g q.2 then 1 else 0) /
                  (D.ZG H u.1 * (1 - D.Δ)) := by
              rw [hPostEq, if_pos hOmit]
              field_simp [ne_of_gt hZUpos, ne_of_gt hCoef]
        · have hZero : (D.anchorU H u.1 q.1).w q.2 = 0 := by
            rw [hAnchorFormula]
            simp [hOwn]
          rw [hZero]
          simp only [mul_zero]
          apply div_nonneg
          · exact mul_nonneg
              (mul_nonneg (D.postW_nonneg _ _) ((D.M.μ q.1).nonneg q.2))
              (ind_nonneg _)
          · exact mul_nonneg hZUpos.le hCoef.le
      have hA : 0 ≤ D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
          if D.omitHit Θ u.1 g q.2 then 1 else 0 := by
        exact mul_nonneg
          (mul_nonneg (D.postW_nonneg _ _) ((D.M.μ q.1).nonneg q.2))
          (ind_nonneg _)
      have hZCoef : 0 < D.ZG H u.1 * (1 - D.Δ) := mul_pos hZUpos hCoef
      have hFactor : Lx ≤ (2 : ℝ) ^ (h + 2) * (D.ZG H u.1 * (1 - D.Δ)) := by
        have hPowH : 0 ≤ (2 : ℝ) ^ h := pow_nonneg (by norm_num) _
        have hPowAG : 0 ≤ (2 : ℝ) ^ h * D.AG u.1 := mul_nonneg hPowH (hAG u.1).le
        have hConst1 : (11 / 10 : ℝ) ≤ 3 / 2 := by norm_num
        have hConst2 : (3 / 2 : ℝ) ≤ 8 / 5 := by norm_num
        have hMultLower : (8 / 10 : ℝ) * D.AG u.1 * (1 / 2) ≤
            D.ZG H u.1 * (1 - D.Δ) :=
          mul_le_mul hZUlower hCoefHalf (by norm_num) hZUpos.le
        calc
          Lx ≤ (11 / 10 : ℝ) * ((2 : ℝ) ^ h * D.AG u.1) := by
            simpa [mul_assoc] using hLxUpper
          _ ≤ (3 / 2 : ℝ) * ((2 : ℝ) ^ h * D.AG u.1) :=
            mul_le_mul_of_nonneg_right hConst1 hPowAG
          _ ≤ (8 / 5 : ℝ) * ((2 : ℝ) ^ h * D.AG u.1) :=
            mul_le_mul_of_nonneg_right hConst2 hPowAG
          _ = (2 : ℝ) ^ (h + 2) * ((8 / 10 : ℝ) * D.AG u.1 * (1 / 2)) := by
            rw [pow_add]
            norm_num
            ring
          _ ≤ (2 : ℝ) ^ (h + 2) * (D.ZG H u.1 * (1 - D.Δ)) :=
            mul_le_mul_of_nonneg_left hMultLower (pow_nonneg (by norm_num) _)
      have hScale :
          (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
            if D.omitHit Θ u.1 g q.2 then 1 else 0) /
              (D.ZG H u.1 * (1 - D.Δ)) ≤
            ((2 : ℝ) ^ (h + 2) *
              (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
                if D.omitHit Θ u.1 g q.2 then 1 else 0)) / Lx := by
        apply (div_le_div_iff₀ hZCoef hLxPos).2
        calc
          (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
              if D.omitHit Θ u.1 g q.2 then 1 else 0) * Lx ≤
            (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
              if D.omitHit Θ u.1 g q.2 then 1 else 0) *
                ((2 : ℝ) ^ (h + 2) * (D.ZG H u.1 * (1 - D.Δ))) :=
            mul_le_mul_of_nonneg_left hFactor hA
          _ = ((2 : ℝ) ^ (h + 2) *
              (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
                if D.omitHit Θ u.1 g q.2 then 1 else 0)) *
                (D.ZG H u.1 * (1 - D.Δ)) := by ring
      calc
        (D.tilt H u.1).w q.1 * (D.anchorU H u.1 q.1).w q.2 ≤
            (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
              if D.omitHit Θ u.1 g q.2 then 1 else 0) /
                (D.ZG H u.1 * (1 - D.Δ)) := hNumBound
        _ ≤ ((2 : ℝ) ^ (h + 2) *
              (D.postW (Θ u.1) q.1 * (D.M.μ q.1).w q.2 *
                if D.omitHit Θ u.1 g q.2 then 1 else 0)) / Lx := hScale
        _ = (2 : ℝ) ^ (h + 2) * (D.refCross Θ g u.1).w q := by
          rw [hNormRefCross q]
          ring

/-- L8.1e(ii) (08:162–163, 179–180): `Mden` does not read `Θ_g`; on the gate the true hypothetical data weight at
`Θ[g ↦ ξ]` is `F_ξ Q` (densities bounded, so no reference vanishes where data has mass), hence
`E_ξ q_{g,k} = Σ_o Q(o) M(o) 1[M(o) < ε₀] ≤ ε₀` (Lemma 3.7, first assertion). -/
theorem den_tail (D : Ctx η₀ β p h) (hd : D.DensityBounds) : D.DenTail := by
  intro Θ g k
  have hgNot : g ∉ crossKeys g := by
    have hdiag : keyDist g g = 0 := by
      unfold keyDist
      simp
    unfold crossKeys
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdiag]
    norm_num
  have hCrossHitUpdate (ζ : D.Tup) (x : Fin D.N) :
      D.crossHit (Function.update Θ g ζ) g x = D.crossHit Θ g x := by
    apply propext
    constructor
    · intro hh u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        exact hgNot hu
      have hval : Function.update Θ g ζ u = Θ u := by simp [hne]
      simpa [hval] using hh u hu
    · intro hh u hu
      have hne : u ≠ g := by
        intro heq
        subst u
        exact hgNot hu
      have hval : Function.update Θ g ζ u = Θ u := by simp [hne]
      simpa [hval] using hh u hu
  have hDMinusUpdate (ζ : D.Tup) (i : D.M.ι) :
      D.dMinus (Function.update Θ g ζ) g i = D.dMinus Θ g i := by
    simp [Ctx.dMinus, hCrossHitUpdate]
  have hRefIntUpdate (ζ : D.Tup) (i : D.M.ι) :
      (D.refInt (Function.update Θ g ζ) g).w i = (D.refInt Θ g).w i := by
    simp [Ctx.refInt, HypercubeRamsey.S08.normOr, hDMinusUpdate]
  have hOmitUpdate (ζ : D.Tup) (u : D.KeyT) (hu : u ∈ crossKeys g) (x : Fin D.N) :
      D.omitHit (Function.update Θ g ζ) u g x = D.omitHit Θ u g x := by
    unfold Ctx.omitHit
    apply propext
    constructor <;> intro hh w hw
    · have hne : w ≠ g := (Finset.mem_erase.mp hw).1
      have hval : Function.update Θ g ζ w = Θ w := by simp [hne]
      simpa [hval] using hh w hw
    · have hne : w ≠ g := (Finset.mem_erase.mp hw).1
      have hval : Function.update Θ g ζ w = Θ w := by simp [hne]
      simpa [hval] using hh w hw
  have hPostUpdate (ζ : D.Tup) (u : D.KeyT) (hu : u ∈ crossKeys g) (i : D.M.ι) :
      D.postW ((Function.update Θ g ζ) u) i = D.postW (Θ u) i := by
    have hne : u ≠ g := by
      intro heq
      subst u
      exact hgNot hu
    simp [hne]
  have hRefCrossUpdate (ζ : D.Tup) (u : D.KeyT) (hu : u ∈ crossKeys g)
      (q : D.M.ι × Fin D.N) :
      (D.refCross (Function.update Θ g ζ) g u).w q = (D.refCross Θ g u).w q := by
    have hraw (q' : D.M.ι × Fin D.N) :
        D.postW (Function.update Θ g ζ u) q'.1 * (D.M.μ q'.1).w q'.2 *
            (if D.omitHit (Function.update Θ g ζ) u g q'.2 then (1 : ℝ) else 0) =
          D.postW (Θ u) q'.1 * (D.M.μ q'.1).w q'.2 *
            (if D.omitHit Θ u g q'.2 then (1 : ℝ) else 0) := by
      rw [hPostUpdate ζ u hu q'.1, hOmitUpdate ζ u hu q'.2]
    have hsum :
        (∑ q' : D.M.ι × Fin D.N,
          D.postW (Function.update Θ g ζ u) q'.1 * (D.M.μ q'.1).w q'.2 *
          (if D.omitHit (Function.update Θ g ζ) u g q'.2 then (1 : ℝ) else 0)) =
        ∑ q' : D.M.ι × Fin D.N, D.postW (Θ u) q'.1 * (D.M.μ q'.1).w q'.2 *
          (if D.omitHit Θ u g q'.2 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro q' _
      exact hraw q'
    simp [Ctx.refCross, HypercubeRamsey.S08.normOr, hraw, hsum]
  have hUpdateTwice (ζ ζ' : D.Tup) :
      Function.update (Function.update Θ g ζ) g ζ' = Function.update Θ g ζ' := by
    funext u
    by_cases hu : u = g <;> simp [Function.update, hu]
  have hFcandUpdate {J : Type} [Fintype J] (ζ ζ' : D.Tup) (o : D.Obs J g) :
      D.Fcand (Function.update Θ g ζ) g ζ' o = D.Fcand Θ g ζ' o := by
    simp [Ctx.Fcand, Ctx.intRatio, Ctx.crossRatio, hUpdateTwice ζ ζ',
      hRefIntUpdate ζ, hRefCrossUpdate ζ]
  have hMdenUpdate {J : Type} [Fintype J] (ζ : D.Tup) (o : D.Obs J g) :
      D.Mden (Function.update Θ g ζ) g o = D.Mden Θ g o := by
    unfold Ctx.Mden
    apply Finset.sum_congr rfl
    intro ζ' _
    rw [hFcandUpdate ζ ζ' o]
  have ratioMul (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ C * b) :
      (a / b) * b = a := by
    by_cases hb0 : b = 0
    · have hab0 : a ≤ 0 := by simpa [hb0] using hab
      have ha0 : a = 0 := le_antisymm hab0 ha
      simp [hb0, ha0]
    · exact div_mul_cancel₀ a hb0
  have hTrueFactor (ζ : D.Tup) (t : Fin k → D.M.ι)
      (c : D.CrossSub g → D.M.ι × Fin D.N)
      (hGate : D.CandGate (Function.update Θ g ζ) g) :
      (if D.CandGate (Function.update Θ g ζ) g then 1 else 0) *
          D.trueW (Function.update Θ g ζ) g t c =
        D.Fcand Θ g ζ ((fun j => some (t j)), c) *
          D.Qref Θ g ((fun j => some (t j)), c) := by
    have hBounds := hd Θ g ζ hGate
    have hIntCancel (j : Fin k) :
        D.intRatio Θ g ζ (some (t j)) * (D.refInt Θ g).w (t j) =
          (D.tilt (Function.update Θ g ζ) g).w (t j) := by
      have hBound := hBounds.1 (t j)
      simpa [Ctx.intRatio] using ratioMul
        ((D.tilt (Function.update Θ g ζ) g).w (t j))
        ((D.refInt Θ g).w (t j))
        (Real.exp (h * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1))
        ((D.tilt (Function.update Θ g ζ) g).nonneg (t j))
        ((D.refInt Θ g).nonneg (t j)) hBound
    have hCrossCancel (u : D.CrossSub g) :
        D.crossRatio Θ g ζ u (c u) * (D.refCross Θ g u.1).w (c u) =
          (D.tilt (Function.update Θ g ζ) u.1).w (c u).1 *
            (D.anchorU (Function.update Θ g ζ) u.1 (c u).1).w (c u).2 := by
      have hBound := hBounds.2 u (c u)
      simpa [Ctx.crossRatio] using ratioMul
        ((D.tilt (Function.update Θ g ζ) u.1).w (c u).1 *
          (D.anchorU (Function.update Θ g ζ) u.1 (c u).1).w (c u).2)
        ((D.refCross Θ g u.1).w (c u))
        ((2 : ℝ) ^ (h + 2))
        (mul_nonneg ((D.tilt (Function.update Θ g ζ) u.1).nonneg (c u).1)
          ((D.anchorU (Function.update Θ g ζ) u.1 (c u).1).nonneg (c u).2))
        ((D.refCross Θ g u.1).nonneg (c u)) hBound
    have hIntProd :
        (∏ j, D.intRatio Θ g ζ (some (t j))) *
          ∏ j, (D.refInt Θ g).w (t j) =
        ∏ j, (D.tilt (Function.update Θ g ζ) g).w (t j) := by
      calc
        _ = ∏ j, D.intRatio Θ g ζ (some (t j)) * (D.refInt Θ g).w (t j) :=
          (Finset.prod_mul_distrib).symm
        _ = ∏ j, (D.tilt (Function.update Θ g ζ) g).w (t j) := by
          apply Finset.prod_congr rfl
          intro j _
          exact hIntCancel j
    have hCrossProd :
        (∏ u, D.crossRatio Θ g ζ u (c u)) *
          ∏ u, (D.refCross Θ g u.1).w (c u) =
        ∏ u, (D.tilt (Function.update Θ g ζ) u.1).w (c u).1 *
          (D.anchorU (Function.update Θ g ζ) u.1 (c u).1).w (c u).2 := by
      calc
        _ = ∏ u, D.crossRatio Θ g ζ u (c u) * (D.refCross Θ g u.1).w (c u) :=
          (Finset.prod_mul_distrib).symm
        _ = ∏ u, (D.tilt (Function.update Θ g ζ) u.1).w (c u).1 *
            (D.anchorU (Function.update Θ g ζ) u.1 (c u).1).w (c u).2 := by
          apply Finset.prod_congr rfl
          intro u _
          exact hCrossCancel u
    by_cases hG : D.CandGate (Function.update Θ g ζ) g
    · have hIntProd' := hIntProd
      have hCrossProd' := hCrossProd
      unfold Ctx.Fcand Ctx.Qref Ctx.trueW
      simp only [if_pos hG, one_mul]
      calc
        (∏ j, (D.tilt (Function.update Θ g ζ) g).w (t j)) *
            ∏ u, (D.tilt (Function.update Θ g ζ) u.1).w (c u).1 *
              (D.anchorU (Function.update Θ g ζ) u.1 (c u).1).w (c u).2 =
          ((∏ j, D.intRatio Θ g ζ (some (t j))) *
              ∏ j, (D.refInt Θ g).w (t j)) *
            ((∏ u, D.crossRatio Θ g ζ u (c u)) *
              ∏ u, (D.refCross Θ g u.1).w (c u)) := by
          rw [← hIntProd', ← hCrossProd']
        _ = ((∏ j, D.intRatio Θ g ζ (some (t j))) *
              ∏ u, D.crossRatio Θ g ζ u (c u)) *
            ((∏ j, (D.refInt Θ g).w (t j)) *
              ∏ u, (D.refCross Θ g u.1).w (c u)) := by ring
    · simp [Ctx.Fcand, hG]
  let obs : (Fin k → D.M.ι) →
      (D.CrossSub g → D.M.ι × Fin D.N) → D.Obs (Fin k) g :=
    fun t c => ((fun j => some (t j)), c)
  let Tlaw : FinProb (Fin k → D.M.ι) := FinProb.pi fun _ => D.refInt Θ g
  let Claw : FinProb (D.CrossSub g → D.M.ι × Fin D.N) :=
    FinProb.pi fun u => D.refCross Θ g u.1
  have hQfactor (t : Fin k → D.M.ι) (c : D.CrossSub g → D.M.ι × Fin D.N) :
      D.Qref Θ g (obs t c) = Tlaw.w t * Claw.w c := by
    simp [Ctx.Qref, obs, Tlaw, Claw, FinProb.pi]
  have hQsum :
      (∑ t : Fin k → D.M.ι, ∑ c : D.CrossSub g → D.M.ι × Fin D.N,
        D.Qref Θ g (obs t c)) = 1 := by
    calc
      _ = ∑ t, ∑ c, Tlaw.w t * Claw.w c := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro c _
        rw [hQfactor]
      _ = ∑ t, Tlaw.w t * (∑ c, Claw.w c) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [← Finset.mul_sum]
      _ = 1 := by simp [Claw.sum_eq_one, Tlaw.sum_eq_one]
  have hExpanded (ζ : D.Tup) :
      D.R'.w ζ * D.qgk (Function.update Θ g ζ) g k =
        ∑ t : Fin k → D.M.ι, ∑ c : D.CrossSub g → D.M.ι × Fin D.N,
          D.R'.w ζ * ((if D.CandGate (Function.update Θ g ζ) g then 1 else 0) *
              D.trueW (Function.update Θ g ζ) g t c *
              if D.Mden (Function.update Θ g ζ) g (obs t c) < D.eps0 then 1 else 0) := by
    unfold Ctx.qgk
    simp only [obs]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  have hBayes : D.R'.expect (fun ζ => D.qgk (Function.update Θ g ζ) g k) =
      ∑ t : Fin k → D.M.ι, ∑ c : D.CrossSub g → D.M.ι × Fin D.N,
        D.Qref Θ g (obs t c) * D.Mden Θ g (obs t c) *
          if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0 := by
    unfold FinProb.expect
    calc
      _ = ∑ ζ, ∑ t, ∑ c, D.R'.w ζ *
          ((if D.CandGate (Function.update Θ g ζ) g then 1 else 0) *
            D.trueW (Function.update Θ g ζ) g t c *
              if D.Mden (Function.update Θ g ζ) g (obs t c) < D.eps0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro ζ _
        exact hExpanded ζ
      _ = ∑ t, ∑ c, ∑ ζ, D.R'.w ζ *
          ((if D.CandGate (Function.update Θ g ζ) g then 1 else 0) *
            D.trueW (Function.update Θ g ζ) g t c *
              if D.Mden (Function.update Θ g ζ) g (obs t c) < D.eps0 then 1 else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_comm]
      _ = ∑ t, ∑ c, D.Qref Θ g (obs t c) * D.Mden Θ g (obs t c) *
          if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro c _
        calc
          _ = (∑ ζ, D.R'.w ζ *
              (D.Fcand Θ g ζ (obs t c) * D.Qref Θ g (obs t c) *
                if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro ζ _
            rw [hMdenUpdate ζ (obs t c)]
            by_cases hGate : D.CandGate (Function.update Θ g ζ) g
            · rw [hTrueFactor ζ t c hGate]
            · simp [hGate, Ctx.Fcand]
          _ = D.Qref Θ g (obs t c) * D.Mden Θ g (obs t c) *
              if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0 := by
            calc
              _ = ∑ ζ, (D.R'.w ζ * D.Fcand Θ g ζ (obs t c)) *
                    (D.Qref Θ g (obs t c) *
                      if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0) := by
                apply Finset.sum_congr rfl
                intro ζ _
                ring
              _ = (∑ ζ, D.R'.w ζ * D.Fcand Θ g ζ (obs t c)) *
                    (D.Qref Θ g (obs t c) *
                      if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0) := by
                rw [Finset.sum_mul]
              _ = _ := by
                change D.Mden Θ g (obs t c) *
                    (D.Qref Θ g (obs t c) *
                      if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0) = _
                ring
  have heps : 0 < D.eps0 := Real.exp_pos _
  have hQnonneg (t : Fin k → D.M.ι) (c : D.CrossSub g → D.M.ι × Fin D.N) :
      0 ≤ D.Qref Θ g (obs t c) := D.Qref_nonneg Θ g (obs t c)
  have hMdenTerm (t : Fin k → D.M.ι) (c : D.CrossSub g → D.M.ι × Fin D.N) :
      D.Qref Θ g (obs t c) * D.Mden Θ g (obs t c) *
          (if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0) ≤
        D.eps0 * D.Qref Θ g (obs t c) := by
    by_cases hm : D.Mden Θ g (obs t c) < D.eps0
    · calc
        _ = D.Qref Θ g (obs t c) * D.Mden Θ g (obs t c) := by simp [hm]
        _ ≤ D.Qref Θ g (obs t c) * D.eps0 :=
          mul_le_mul_of_nonneg_left (le_of_lt hm) (hQnonneg t c)
        _ = D.eps0 * D.Qref Θ g (obs t c) := by ring
    · simp [hm]
      exact mul_nonneg heps.le (hQnonneg t c)
  calc
    D.R'.expect (fun ζ => D.qgk (Function.update Θ g ζ) g k) =
        ∑ t, ∑ c, D.Qref Θ g (obs t c) * D.Mden Θ g (obs t c) *
          if D.Mden Θ g (obs t c) < D.eps0 then 1 else 0 := hBayes
    _ ≤ ∑ t, ∑ c, D.eps0 * D.Qref Θ g (obs t c) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro c _
      exact hMdenTerm t c
    _ = D.eps0 * (∑ t, ∑ c, D.Qref Θ g (obs t c)) := by
      calc
        _ = ∑ t, D.eps0 * (∑ c, D.Qref Θ g (obs t c)) := by
          apply Finset.sum_congr rfl
          intro t _
          rw [← Finset.mul_sum]
        _ = D.eps0 * (∑ t, ∑ c, D.Qref Θ g (obs t c)) := by
          rw [← Finset.mul_sum]
    _ = D.eps0 := by rw [hQsum]; ring

/-- L8.1e(iii) (08:163–169): `N^h R'(ξ) ≤ e^{hn^β}` (width of `ν_i`), `F_ξ ≤ e^{T(hn^β + n^{τ/2} + 1)} 2^{2s(h+2)}`
(density bounds, `|E(g)| ≤ 2s`), and `M ≥ ε₀`; since `T = n^{τ/8 + o(1)}` and `β < τ/4`, the log density is at most
`1.5δhs log n` for large `n`. -/
theorem post_cap (hη₀ : 0 < η₀) (hβ₀ : 0 < β) (hβτ : β < tau8 η₀ / 4) (hh : 1 ≤ h) :
    ∃ n₀ : ℕ, ∀ D : Ctx η₀ β p h, n₀ ≤ D.n → ∀ X Y R : Finset (Fin D.N), Std D γ K X Y R →
      GridFacts η₀ D.n → D.DensityBounds → D.PostCap := by
  have hτ : 0 < tau8 η₀ := tau8_pos hη₀
  have hlogLarge : ∀ᶠ n : ℕ in Filter.atTop, 380000 < Real.log (n : ℝ) := by
    have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (Filter.eventually_gt_atTop 380000)
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hlogLarge
  refine ⟨n₀, ?_⟩
  intro D hn X Y R hStd hGrid hDensity
  have hnNat : 1 ≤ D.n := hGrid.pos.1
  have hnR : 1 ≤ (D.n : ℝ) := by exact_mod_cast hnNat
  have hnPos : 0 < (D.n : ℝ) := lt_of_lt_of_le (by norm_num) hnR
  have hlog : 380000 < Real.log (D.n : ℝ) := hn₀ D.n hn
  have htau8 : 0 < tau8 η₀ / 8 := by positivity
  have htauHalf : 0 < tau8 η₀ / 2 := by positivity
  have hPowTau : 1 ≤ (D.n : ℝ) ^ tau8 η₀ := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR (show (0 : ℝ) ≤ tau8 η₀ by linarith)
    simpa using h
  have hPowTau8 : 1 ≤ (D.n : ℝ) ^ (tau8 η₀ / 8) := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR (show (0 : ℝ) ≤ tau8 η₀ / 8 by positivity)
    simpa using h
  have hSceil : (sC η₀ D.n : ℝ) < (D.n : ℝ) ^ tau8 η₀ + 1 := by
    dsimp [sC]
    exact_mod_cast Nat.ceil_lt_add_one (Real.rpow_nonneg hnPos.le _)
  have hSlow : (D.n : ℝ) ^ tau8 η₀ ≤ (sC η₀ D.n : ℝ) := by
    dsimp [sC]
    exact_mod_cast (Nat.le_ceil ((D.n : ℝ) ^ tau8 η₀))
  have hSupper : (sC η₀ D.n : ℝ) ≤ 2 * (D.n : ℝ) ^ tau8 η₀ := by
    have hs := le_of_lt hSceil
    nlinarith [hPowTau]
  have hTCceil : (TC η₀ D.n : ℝ) < (D.n : ℝ) ^ (tau8 η₀ / 8) + 1 := by
    dsimp [TC]
    exact_mod_cast Nat.ceil_lt_add_one (Real.rpow_nonneg hnPos.le _)
  have hTCupper : (TC η₀ D.n : ℝ) ≤ 2 * (D.n : ℝ) ^ (tau8 η₀ / 8) := by
    have ht := le_of_lt hTCceil
    nlinarith [hPowTau8]
  have hPowBeta : (D.n : ℝ) ^ β ≤ (D.n : ℝ) ^ tau8 η₀ :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hβτ, hτ])
  have hPowBetaTau8 : (D.n : ℝ) ^ (tau8 η₀ / 8 + β) ≤ (D.n : ℝ) ^ tau8 η₀ :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith [hβτ, hτ])
  have hPowTau58 : (D.n : ℝ) ^ (tau8 η₀ / 8 + tau8 η₀ / 2) ≤
      (D.n : ℝ) ^ tau8 η₀ := by
    apply Real.rpow_le_rpow_of_exponent_le hnR
    linarith
  have hPowTauHalf : (D.n : ℝ) ^ (tau8 η₀ / 2) ≤ (D.n : ℝ) ^ tau8 η₀ := by
    apply Real.rpow_le_rpow_of_exponent_le hnR
    linarith
  have hPowTau8Tau : (D.n : ℝ) ^ (tau8 η₀ / 8) ≤ (D.n : ℝ) ^ tau8 η₀ := by
    apply Real.rpow_le_rpow_of_exponent_le hnR
    linarith
  have hTbeta : (TC η₀ D.n : ℝ) * (D.n : ℝ) ^ β ≤ 2 * (D.n : ℝ) ^ tau8 η₀ := by
    calc
      (TC η₀ D.n : ℝ) * (D.n : ℝ) ^ β ≤
          ((D.n : ℝ) ^ (tau8 η₀ / 8) + 1) * (D.n : ℝ) ^ β :=
        mul_le_mul_of_nonneg_right (le_of_lt hTCceil) (Real.rpow_nonneg hnPos.le _)
      _ = (D.n : ℝ) ^ (tau8 η₀ / 8 + β) + (D.n : ℝ) ^ β := by
        rw [add_mul, ← Real.rpow_add hnPos]
        ring
      _ ≤ (D.n : ℝ) ^ tau8 η₀ + (D.n : ℝ) ^ tau8 η₀ :=
        add_le_add hPowBetaTau8 hPowBeta
      _ = 2 * (D.n : ℝ) ^ tau8 η₀ := by ring
  have hTtauHalf : (TC η₀ D.n : ℝ) * (D.n : ℝ) ^ (tau8 η₀ / 2) ≤
      2 * (D.n : ℝ) ^ tau8 η₀ := by
    calc
      (TC η₀ D.n : ℝ) * (D.n : ℝ) ^ (tau8 η₀ / 2) ≤
          ((D.n : ℝ) ^ (tau8 η₀ / 8) + 1) * (D.n : ℝ) ^ (tau8 η₀ / 2) :=
        mul_le_mul_of_nonneg_right (le_of_lt hTCceil) (Real.rpow_nonneg hnPos.le _)
      _ = (D.n : ℝ) ^ (tau8 η₀ / 8 + tau8 η₀ / 2) +
          (D.n : ℝ) ^ (tau8 η₀ / 2) := by
        rw [add_mul, ← Real.rpow_add hnPos]
        ring
      _ ≤ (D.n : ℝ) ^ tau8 η₀ + (D.n : ℝ) ^ tau8 η₀ :=
        add_le_add hPowTau58 hPowTauHalf
      _ = 2 * (D.n : ℝ) ^ tau8 η₀ := by ring
  have hTone : (TC η₀ D.n : ℝ) ≤ 2 * (D.n : ℝ) ^ tau8 η₀ := by
    calc
      (TC η₀ D.n : ℝ) ≤ (D.n : ℝ) ^ (tau8 η₀ / 8) + 1 := le_of_lt hTCceil
      _ ≤ (D.n : ℝ) ^ tau8 η₀ + (D.n : ℝ) ^ tau8 η₀ := by
        exact add_le_add hPowTau8Tau hPowTau
      _ = 2 * (D.n : ℝ) ^ tau8 η₀ := by ring
  have hTbase : (TC η₀ D.n : ℝ) *
      ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) ≤
      (2 * (h : ℝ) + 4) * (D.n : ℝ) ^ tau8 η₀ := by
    rw [mul_add, mul_add]
    nlinarith [hTbeta, hTtauHalf, hTone, (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
  have hhn : (h : ℝ) * (D.n : ℝ) ^ β ≤ (h : ℝ) * (D.n : ℝ) ^ tau8 η₀ :=
    mul_le_mul_of_nonneg_left hPowBeta (Nat.cast_nonneg h)
  have hCrossExp : (2 : ℝ) * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ) ≤
      4 * ((h + 2 : ℕ) : ℝ) * (D.n : ℝ) ^ tau8 η₀ := by
    have hh2 : 0 ≤ ((h + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hSupper (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hh2)]
  have hOverhead :
      (h : ℝ) * (D.n : ℝ) ^ β +
        (TC η₀ D.n : ℝ) * ((h : ℝ) * (D.n : ℝ) ^ β +
          (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) +
        (2 : ℝ) * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ) ≤
      (19 : ℝ) * (h : ℝ) * (D.n : ℝ) ^ tau8 η₀ := by
    calc
      _ ≤ ((h : ℝ) + (2 * (h : ℝ) + 4) + 4 * ((h + 2 : ℕ) : ℝ)) *
            (D.n : ℝ) ^ tau8 η₀ := by
        nlinarith [hhn, hTbase, hCrossExp]
      _ ≤ 19 * (h : ℝ) * (D.n : ℝ) ^ tau8 η₀ := by
        have hhreal : 1 ≤ (h : ℝ) := by exact_mod_cast hh
        have hplus2 : ((h + 2 : ℕ) : ℝ) = (h : ℝ) + 2 := by norm_num
        rw [hplus2]
        nlinarith [hhreal, Real.rpow_nonneg hnPos.le (tau8 η₀)]
  have h19 : 19 ≤ (1 / 20000 : ℝ) * Real.log (D.n : ℝ) := by
    have hh := mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 1 / 20000)
    norm_num at hh
    exact le_of_lt hh
  have hBudget : (19 : ℝ) * (h : ℝ) * (D.n : ℝ) ^ tau8 η₀ ≤
      (1 / 20000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) := by
    have hcoef : 0 ≤ (1 / 20000 : ℝ) * Real.log (D.n : ℝ) := by positivity
    calc
      (19 : ℝ) * (h : ℝ) * (D.n : ℝ) ^ tau8 η₀ ≤
          ((1 / 20000 : ℝ) * Real.log (D.n : ℝ)) *
            ((h : ℝ) * (D.n : ℝ) ^ tau8 η₀) := by
        calc
          _ = 19 * ((h : ℝ) * (D.n : ℝ) ^ tau8 η₀) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h19
            (mul_nonneg (Nat.cast_nonneg h) (Real.rpow_nonneg hnPos.le _))
      _ ≤ ((1 / 20000 : ℝ) * Real.log (D.n : ℝ)) *
            ((h : ℝ) * (sC η₀ D.n : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hSlow (Nat.cast_nonneg h)) hcoef
      _ = (1 / 20000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) := by ring
  have hExpBudget :
      (h : ℝ) * (D.n : ℝ) ^ β +
        (TC η₀ D.n : ℝ) * ((h : ℝ) * (D.n : ℝ) ^ β +
          (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) +
        (2 : ℝ) * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ) +
        (1 / 10000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) ≤
      (15 / 100000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) := by
    calc
      _ ≤ 19 * (h : ℝ) * (D.n : ℝ) ^ tau8 η₀ +
          (1 / 10000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) :=
        by nlinarith only [hOverhead]
      _ ≤ (1 / 20000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) +
          (1 / 10000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) :=
        by nlinarith only [hBudget]
      _ = (15 / 100000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ) := by ring
  have hNposPow : 0 < (D.N : ℝ) ^ h := pow_pos (by exact_mod_cast hStd.size.1) _
  have hRformula (ξ : D.Tup) :
      D.R'.w ξ = ∑ i, D.M.Λ i * ∏ j, (D.M.ν i).w (ξ j) := by
    simp only [Ctx.R', FinProb.map, FinProb.bind, FinProb.pi]
    rw [Fintype.sum_prod_type]
    simp [Ctx.tagLaw]
  have hRcap (ξ : D.Tup) :
      D.R'.w ξ ≤ ((Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h) := by
    rw [hRformula ξ]
    calc
      (∑ i, D.M.Λ i * ∏ j, (D.M.ν i).w (ξ j)) ≤
          ∑ i, D.M.Λ i * ((Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hΛ : 0 < D.M.Λ i
        · obtain ⟨_, hνsupp, _, hνwidth, _⟩ := hStd.laws i hΛ
          have hνprod : (∏ j, (D.M.ν i).w (ξ j)) ≤
              (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h := by
            calc
              (∏ j, (D.M.ν i).w (ξ j)) ≤
                  ∏ j, Real.exp ((D.n : ℝ) ^ β) / D.N := by
                apply Finset.prod_le_prod₀
                · intro j _
                  exact (D.M.ν i).nonneg (ξ j)
                · intro j _
                  exact hνwidth (ξ j)
              _ = (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h := by
                simp [Finset.prod_const, div_pow]
          exact mul_le_mul_of_nonneg_left hνprod (D.M.Λ_nonneg i)
        · have hΛ0 : D.M.Λ i = 0 := by
            exact le_antisymm (le_of_not_gt hΛ) (D.M.Λ_nonneg i)
          simp [hΛ0]
      _ = (Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h := by
        rw [← Finset.sum_mul, D.M.Λ_sum]
        ring
  have hRscale (ξ : D.Tup) : (D.N : ℝ) ^ h * D.R'.w ξ ≤ Real.exp ((h : ℝ) * (D.n : ℝ) ^ β) := by
    have hNneq : (D.N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hStd.size.1)
    calc
      (D.N : ℝ) ^ h * D.R'.w ξ ≤
          (D.N : ℝ) ^ h * ((Real.exp ((D.n : ℝ) ^ β) / D.N) ^ h) :=
        mul_le_mul_of_nonneg_left (hRcap ξ) (pow_nonneg (by exact_mod_cast hStd.size.1.le) _)
      _ = Real.exp ((h : ℝ) * (D.n : ℝ) ^ β) := by
        rw [div_pow, ← Real.exp_nat_mul]
        field_simp [hNneq]
  have hdivBound {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 1 ≤ C)
      (hab : a ≤ C * b) : a / b ≤ C := by
    by_cases hb0 : b = 0
    · have ha0 : a = 0 := by
        apply le_antisymm
        · simpa [hb0] using hab
        · exact ha
      simp [hb0, ha0]
      exact le_trans (by norm_num) hC
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      exact (div_le_iff₀ hbpos).2 (by simpa [mul_comm] using hab)
  have hA :
      1 ≤ (h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1 := by
    have hpow : 0 ≤ (D.n : ℝ) ^ (tau8 η₀ / 2) := Real.rpow_nonneg hnPos.le _
    have hbeta : 0 ≤ (D.n : ℝ) ^ β := Real.rpow_nonneg hnPos.le _
    have hhNonneg : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
    linarith only [mul_nonneg hhNonneg hbeta, hpow]
  let Cint : ℝ := Real.exp ((h : ℝ) * (D.n : ℝ) ^ β +
    (D.n : ℝ) ^ (tau8 η₀ / 2) + 1)
  let Ccross : ℝ := (2 : ℝ) ^ (h + 2)
  have hCintOne : 1 ≤ Cint := by
    dsimp [Cint]
    calc
      1 = Real.exp 0 := by simp
      _ ≤ Real.exp ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) :=
        Real.exp_le_exp.mpr (by linarith [hA])
  have hCcrossOne : 1 ≤ Ccross := by
    dsimp [Ccross]
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hFbound (g : D.KeyT) (Θ : D.Hist) (o : D.Obs D.Loc g)
      (hcount : (Finset.univ.filter fun ℓ => (o.1 ℓ).isSome).card ≤ TC η₀ D.n)
      (hmass : D.eps0 ≤ D.Mden Θ g o) (ξ : D.Tup) :
      (D.N : ℝ) ^ h * (D.basePost Θ g o).w ξ ≤
        Real.exp ((15 / 100000 : ℝ) * (h : ℝ) *
          sC η₀ D.n * Real.log D.n) := by
    have heps : 0 < D.eps0 := Real.exp_pos _
    have hMpos : 0 < D.Mden Θ g o := lt_of_lt_of_le heps hmass
    have hbase : (D.basePost Θ g o).w ξ =
        D.R'.w ξ * D.Fcand Θ g ξ o / D.Mden Θ g o := by
      unfold Ctx.basePost
      simp only [HypercubeRamsey.S08.normOr]
      have hsumne : (∑ ξ', D.R'.w ξ' * D.Fcand Θ g ξ' o) ≠ 0 := by
        change D.Mden Θ g o ≠ 0
        exact ne_of_gt hMpos
      rw [if_neg hsumne]
      simp [Ctx.Mden]
    have hIntEach (hCand : D.CandGate (Function.update Θ g ξ) g) (j : D.Loc) :
      0 ≤ D.intRatio Θ g ξ (o.1 j) ∧
        D.intRatio Θ g ξ (o.1 j) ≤ Cint := by
      constructor
      · exact D.intRatio_nonneg Θ g ξ (o.1 j)
      · cases hopt : o.1 j with
        | none =>
          simp [Ctx.intRatio, hopt]
          exact hCintOne
        | some i =>
          have hDens := hDensity Θ g ξ hCand
          simpa [Ctx.intRatio, Cint] using hdivBound ((D.tilt (Function.update Θ g ξ) g).nonneg i)
            ((D.refInt Θ g).nonneg i) hCintOne (hDens.1 i)
    have hCrossEach (hCand : D.CandGate (Function.update Θ g ξ) g) (u : D.CrossSub g) :
        0 ≤ D.crossRatio Θ g ξ u (o.2 u) ∧ D.crossRatio Θ g ξ u (o.2 u) ≤ Ccross := by
      constructor
      · exact D.crossRatio_nonneg Θ g ξ u (o.2 u)
      · have hraw :
            (D.tilt (Function.update Θ g ξ) u.1).w (o.2 u).1 *
                (D.anchorU (Function.update Θ g ξ) u.1 (o.2 u).1).w (o.2 u).2 ≤
              Ccross * (D.refCross Θ g u.1).w (o.2 u) := by
          simpa [Ccross] using (hDensity Θ g ξ hCand).2 u (o.2 u)
        exact hdivBound
          (mul_nonneg ((D.tilt (Function.update Θ g ξ) u.1).nonneg (o.2 u).1)
            ((D.anchorU (Function.update Θ g ξ) u.1 (o.2 u).1).nonneg (o.2 u).2))
          ((D.refCross Θ g u.1).nonneg (o.2 u)) hCcrossOne
          hraw
    have hProdInt (hCand : D.CandGate (Function.update Θ g ξ) g) :
        (∏ j : D.Loc, D.intRatio Θ g ξ (o.1 j)) ≤ Cint ^ (TC η₀ D.n) := by
      let S : Finset D.Loc := Finset.univ.filter fun j => (o.1 j).isSome
      have hfilter : (∏ j : D.Loc, D.intRatio Θ g ξ (o.1 j)) =
          ∏ j ∈ S, D.intRatio Θ g ξ (o.1 j) := by
        have hfilter' :
            (∏ j ∈ Finset.univ with (o.1 j).isSome, D.intRatio Θ g ξ (o.1 j)) =
              ∏ j : D.Loc, D.intRatio Θ g ξ (o.1 j) :=
          Finset.prod_filter_of_ne (s := Finset.univ)
            (p := fun j : D.Loc => (o.1 j).isSome)
            (f := fun j => D.intRatio Θ g ξ (o.1 j)) (by
              intro j hj hne
              cases hopt : o.1 j with
              | none => simp [Ctx.intRatio, hopt] at hne
              | some i => simp [hopt])
        simpa [S] using hfilter'.symm
      have hS : S.card ≤ TC η₀ D.n := by simpa [S] using hcount
      calc
        _ = ∏ j ∈ S, D.intRatio Θ g ξ (o.1 j) := hfilter
        _ ≤ ∏ j ∈ S, Cint := by
          apply Finset.prod_le_prod₀
          · intro j hj
            exact (hIntEach hCand j).1
          · intro j hj
            exact (hIntEach hCand j).2
        _ = Cint ^ S.card := by simp [Finset.prod_const]
        _ ≤ Cint ^ (TC η₀ D.n) := pow_le_pow_right₀ hCintOne hS
    have hcardCross : Fintype.card (D.CrossSub g) ≤ 2 * sC η₀ D.n := by
      have hcard := hGrid.crossKeys_card g
      simpa [Ctx.CrossSub] using hcard
    have hProdCross (hCand : D.CandGate (Function.update Θ g ξ) g) :
        (∏ u : D.CrossSub g, D.crossRatio Θ g ξ u (o.2 u)) ≤
          Ccross ^ (2 * sC η₀ D.n) := by
      calc
        (∏ u : D.CrossSub g, D.crossRatio Θ g ξ u (o.2 u)) ≤
            Ccross ^ Fintype.card (D.CrossSub g) := by
          calc
            _ ≤ ∏ u : D.CrossSub g, Ccross := by
              apply Finset.prod_le_prod₀
              · intro u hu
                exact (hCrossEach hCand u).1
              · intro u hu
                exact (hCrossEach hCand u).2
            _ = Ccross ^ Fintype.card (D.CrossSub g) := by simp [Finset.prod_const]
        _ ≤ Ccross ^ (2 * sC η₀ D.n) := pow_le_pow_right₀ hCcrossOne hcardCross
    have hTwoExp (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
      calc
        (2 : ℝ) ^ m ≤ (Real.exp 1) ^ m := by
          gcongr
          exact Real.exp_one_gt_two.le
        _ = Real.exp (m : ℝ) := by
          rw [← Real.exp_nat_mul]
          simp
    have hFcand : D.Fcand Θ g ξ o ≤
        Real.exp ((TC η₀ D.n : ℝ) *
            ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) +
          2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ)) := by
      by_cases hCand : D.CandGate (Function.update Θ g ξ) g
      · have hDens := hDensity Θ g ξ hCand
        have hIntNonneg : 0 ≤ ∏ j : D.Loc, D.intRatio Θ g ξ (o.1 j) :=
          Finset.prod_nonneg fun j _ => (hIntEach hCand j).1
        have hCrossNonneg : 0 ≤ ∏ u : D.CrossSub g, D.crossRatio Θ g ξ u (o.2 u) :=
          Finset.prod_nonneg fun u _ => (hCrossEach hCand u).1
        have hprodBound : D.Fcand Θ g ξ o ≤ Cint ^ (TC η₀ D.n) * Ccross ^ (2 * sC η₀ D.n) := by
          unfold Ctx.Fcand
          simp [hCand]
          calc
            (∏ j : D.Loc, D.intRatio Θ g ξ (o.1 j)) *
                ∏ u : D.CrossSub g, D.crossRatio Θ g ξ u (o.2 u) ≤
              Cint ^ (TC η₀ D.n) * ∏ u : D.CrossSub g, D.crossRatio Θ g ξ u (o.2 u) :=
                mul_le_mul_of_nonneg_right (hProdInt hCand) hCrossNonneg
            _ ≤ Cint ^ (TC η₀ D.n) * Ccross ^ (2 * sC η₀ D.n) :=
              mul_le_mul_of_nonneg_left (hProdCross hCand)
                (pow_nonneg (Real.exp_nonneg _) _)
        have hCintpow : Cint ^ (TC η₀ D.n) =
            Real.exp ((TC η₀ D.n : ℝ) *
              ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1)) := by
          dsimp [Cint]
          rw [← Real.exp_nat_mul]
        have hCcrosspow : Ccross ^ (2 * sC η₀ D.n) ≤
            Real.exp (2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ)) := by
          have hp := hTwoExp ((h + 2) * (2 * sC η₀ D.n))
          have hcast : (((h + 2) * (2 * sC η₀ D.n) : ℕ) : ℝ) =
              2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ) := by push_cast; ring
          calc
            Ccross ^ (2 * sC η₀ D.n) =
                (2 : ℝ) ^ ((h + 2) * (2 * sC η₀ D.n)) := by
              simp [Ccross, pow_mul]
            _ ≤ Real.exp (((h + 2) * (2 * sC η₀ D.n) : ℕ) : ℝ) := hp
            _ = Real.exp (2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ)) := by rw [hcast]
        calc
          D.Fcand Θ g ξ o ≤ Cint ^ (TC η₀ D.n) * Ccross ^ (2 * sC η₀ D.n) := hprodBound
          _ ≤ Real.exp ((TC η₀ D.n : ℝ) *
                ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1)) *
              Real.exp (2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ)) :=
            mul_le_mul hCintpow.le hCcrosspow (by positivity) (by positivity)
          _ = _ := by rw [← Real.exp_add]
      · simp [Ctx.Fcand, hCand]
        exact le_of_lt (Real.exp_pos _)
    have hbasePost : (D.N : ℝ) ^ h * (D.basePost Θ g o).w ξ ≤
        Real.exp ((h : ℝ) * (D.n : ℝ) ^ β +
          (TC η₀ D.n : ℝ) * ((h : ℝ) * (D.n : ℝ) ^ β +
            (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) +
          2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ) +
          (1 / 10000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ)) := by
      rw [hbase]
      have hRbound := hRscale ξ
      have hFnonneg : 0 ≤ D.Fcand Θ g ξ o := D.Fcand_nonneg Θ g ξ o
      have hMInv : (D.Mden Θ g o)⁻¹ ≤ D.eps0⁻¹ :=
        (inv_le_inv₀ hMpos heps).2 hmass
      have hEpsInv : D.eps0⁻¹ = Real.exp ((1 / 10000 : ℝ) * (h : ℝ) *
          (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ)) := by
        unfold Ctx.eps0
        rw [Real.exp_neg]
        simp
      calc
        (D.N : ℝ) ^ h * (D.R'.w ξ * D.Fcand Θ g ξ o / D.Mden Θ g o) =
            ((D.N : ℝ) ^ h * D.R'.w ξ) * D.Fcand Θ g ξ o * (D.Mden Θ g o)⁻¹ := by ring
        _ ≤ Real.exp ((h : ℝ) * (D.n : ℝ) ^ β) * D.Fcand Θ g ξ o * D.eps0⁻¹ := by
          have hfirst := mul_le_mul_of_nonneg_right hRbound hFnonneg
          have hMInvNonneg : 0 ≤ (D.Mden Θ g o)⁻¹ := inv_nonneg.mpr hMpos.le
          have hsecond := mul_le_mul_of_nonneg_left hMInv
            (mul_nonneg (Real.exp_nonneg ((h : ℝ) * (D.n : ℝ) ^ β)) hFnonneg)
          calc
            _ = (((D.N : ℝ) ^ h * D.R'.w ξ) * D.Fcand Θ g ξ o) *
                  (D.Mden Θ g o)⁻¹ := by ring
            _ ≤ (Real.exp ((h : ℝ) * (D.n : ℝ) ^ β) * D.Fcand Θ g ξ o) *
                  (D.Mden Θ g o)⁻¹ :=
              mul_le_mul_of_nonneg_right hfirst hMInvNonneg
            _ ≤ (Real.exp ((h : ℝ) * (D.n : ℝ) ^ β) * D.Fcand Θ g ξ o) * D.eps0⁻¹ := by
              exact hsecond
        _ ≤ Real.exp ((h : ℝ) * (D.n : ℝ) ^ β) *
              Real.exp ((TC η₀ D.n : ℝ) *
                ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) +
                2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ)) * D.eps0⁻¹ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hFcand (Real.exp_nonneg _)) (by positivity)
        _ = Real.exp ((h : ℝ) * (D.n : ℝ) ^ β +
              (TC η₀ D.n : ℝ) *
                ((h : ℝ) * (D.n : ℝ) ^ β + (D.n : ℝ) ^ (tau8 η₀ / 2) + 1) +
              2 * (sC η₀ D.n : ℝ) * ((h + 2 : ℕ) : ℝ) +
              (1 / 10000 : ℝ) * (h : ℝ) * (sC η₀ D.n : ℝ) * Real.log (D.n : ℝ)) := by
          rw [hEpsInv]
          rw [← Real.exp_add]
          rw [← Real.exp_add]
          congr 1
          ring
    exact le_trans hbasePost (Real.exp_le_exp.mpr hExpBudget)
  intro Θ g o hcount hmass ξ
  exact hFbound g Θ o hcount hmass ξ

/-- L8.1e(iv) (08:171–176): a candidate with `F_ξ ≠ 0` passes its gates, so `Z_u > 0` and every observed cross tag
passes the cutoffs at `u` (`d^+ ≥ (1-Δ)e^{-n^{2τ}} > 0`), so `U_{u,i}` is the conditioned law and the observed
cross anchor hits `Θ_g = ξ` (as `g ∈ E(u)`); likewise each observed internal tag passes the cutoffs at `g`. -/
theorem f_support (D : Ctx η₀ β p h) (hn : 1 ≤ D.n) : D.FSupport := by
  unfold Ctx.FSupport
  intro J inst Θ g ξ o hF
  let H : D.Hist := Function.update Θ g ξ
  have hCand : D.CandGate H g := by
    by_contra hnot
    apply hF
    unfold Ctx.Fcand
    rw [if_neg hnot]
    simp
  have hInt (j : J) : D.intRatio Θ g ξ (o.1 j) ≠ 0 := by
    by_contra hz
    have hzprod : (∏ k, D.intRatio Θ g ξ (o.1 k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hz
    apply hF
    unfold Ctx.Fcand
    rw [if_pos hCand, hzprod]
    simp
  have hCross (u : D.CrossSub g) : D.crossRatio Θ g ξ u (o.2 u) ≠ 0 := by
    by_contra hz
    have hzprod : (∏ v, D.crossRatio Θ g ξ v (o.2 v)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ u) hz
    apply hF
    unfold Ctx.Fcand
    rw [if_pos hCand, hzprod]
    simp
  have hOpenOfTilt (u : D.KeyT) (i : D.M.ι) (hBase : D.BaseGates H u)
      (hTilt : (D.tilt H u).w i ≠ 0) : D.GateOpen H u i := by
    have hAG : 0 < D.AG u := by
      unfold Ctx.AG
      positivity
    have hZ : 0 < D.ZG H u :=
      lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8 / 10) hAG) hBase.2.1.1
    have hsum : (∑ i', D.tiltW H u i') ≠ 0 := by
      intro hz
      apply (ne_of_gt hZ)
      simpa [Ctx.ZG] using hz
    have hnorm (i' : D.M.ι) : (D.tilt H u).w i' = D.tiltW H u i' / D.ZG H u := by
      simp [Ctx.tilt, HypercubeRamsey.S08.normOr, Ctx.ZG, hsum]
    have hweight : D.tiltW H u i ≠ 0 := by
      intro hz
      apply hTilt
      rw [hnorm i, hz]
      simp
    by_contra hnot
    apply hweight
    simp [Ctx.tiltW, hnot]
  have hKeyDistSymm (u v : D.KeyT) : keyDist u v = keyDist v u := by
    unfold keyDist
    apply Finset.sum_congr rfl
    intro r _
    exact Nat.dist_comm _ _
  have hCrossSymm (u : D.KeyT) (hu : u ∈ crossKeys g) : g ∈ crossKeys u := by
    have hu' : keyDist g u = 1 := by simpa [crossKeys] using hu
    have hg' : keyDist u g = 1 := by rw [hKeyDistSymm]; exact hu'
    simpa [crossKeys] using hg'
  have hnR : 0 < (D.n : ℝ) := by exact_mod_cast (by omega : 0 < D.n)
  have hpowPos : 0 < (D.n : ℝ) ^ (p / 2) := Real.rpow_pos_of_pos hnR _
  have hDelta : D.Δ < 1 := by
    unfold Ctx.Δ
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hpowPos)
  have hCut : 0 < D.cut := Real.exp_pos _
  refine ⟨?_, ?_⟩
  · intro u
    let q := o.2 u
    have hratio := hCross u
    have hTilt : (D.tilt H u.1).w q.1 ≠ 0 := by
      by_contra hz
      have hz' : (D.tilt (Function.update Θ g ξ) u.1).w q.1 = 0 := by
        simpa [H, q] using hz
      apply hratio
      unfold Ctx.crossRatio
      rw [hz']
      simp
    have hBase : D.BaseGates H u.1 := hCand.2 u.1 u.2
    have hOpen := hOpenOfTilt u.1 q.1 hBase hTilt
    have hDMinus : 0 < D.dMinus H u.1 q.1 := lt_of_lt_of_le hCut hOpen.1
    have hDPlus : 0 < D.dPlus H u.1 q.1 :=
      lt_of_lt_of_le (mul_pos (sub_pos.mpr hDelta) hDMinus) hOpen.2
    have hAnchor : (D.anchorU H u.1 q.1).w q.2 ≠ 0 := by
      intro hz
      have hz' : (D.anchorU (Function.update Θ g ξ) u.1 q.1).w q.2 = 0 := by
        simpa [H, q] using hz
      apply hratio
      unfold Ctx.crossRatio
      rw [hz']
      simp
    have hsumNe : (∑ x, if D.ownHit H u.1 x then (D.M.μ q.1).w x else 0) ≠ 0 := by
      simpa [Ctx.dPlus] using ne_of_gt hDPlus
    have hAnchorFormula : (D.anchorU H u.1 q.1).w q.2 =
        ((D.M.μ q.1).w q.2 * if D.ownHit H u.1 q.2 then 1 else 0) /
          D.dPlus H u.1 q.1 := by
      change (if (∑ x, (D.M.μ q.1).w x * if D.ownHit H u.1 x then 1 else 0) = 0 then
        (D.M.μ q.1).w q.2 else
        ((D.M.μ q.1).w q.2 * if D.ownHit H u.1 q.2 then 1 else 0) /
          (∑ x, (D.M.μ q.1).w x * if D.ownHit H u.1 x then 1 else 0)) =
        ((D.M.μ q.1).w q.2 * if D.ownHit H u.1 q.2 then 1 else 0) /
          D.dPlus H u.1 q.1
      rw [if_neg (by simpa using hsumNe)]
      rfl
    have hOwn : D.ownHit H u.1 q.2 := by
      by_contra hnot
      have hz : (D.anchorU H u.1 q.1).w q.2 = 0 := by
        rw [hAnchorFormula]
        simp [hnot]
      exact hAnchor hz
    have hhit := hOwn.1 g (hCrossSymm u.1 u.2)
    simpa [H] using hhit
  · intro j i hsome
    have hratio := hInt j
    rw [hsome] at hratio
    have hTilt : (D.tilt H g).w i ≠ 0 := by
      by_contra hz
      have hz' : (D.tilt (Function.update Θ g ξ) g).w i = 0 := by
        simpa [H] using hz
      apply hratio
      unfold Ctx.intRatio
      simp [hz']
    exact hOpenOfTilt g i hCand.1 hTilt

end Nodes

end HypercubeRamsey.S08
