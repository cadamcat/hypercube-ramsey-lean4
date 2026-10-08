import HypercubeRamsey.S18.Nodes_sol_s18_2lm_iteration
import HypercubeRamsey.S18.Nodes_sol_fix_outsupp

namespace HypercubeRamsey.S18.Lane_sol_s18_2lm.Witnesses

open Classical Filter
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
  {hPT : PT.Valid} {D : LateData hPT} {X : CriticalTransferData D}

noncomputable def patchLaw (X : CriticalTransferData D) : FinLaw (Fin (T.S.N k)) :=
  FinLaw.uniform (PT.tiling.P (D.geom.patchOf X.target)).X (hPT.tiling_valid.patch_nonempty _).1

/-- A finite law for the independently chosen singleton or pair witness,
with the option tag fixed by the witness type. -/
noncomputable def law (X : CriticalTransferData D) (pair : Bool) :
    FinLaw (Fin (T.S.N k) × Option (Fin (T.S.N k))) where
  w xz := if pair then match xz.2 with
    | none => 0
    | some z => (patchLaw X).w xz.1 * (patchLaw X).w z
    else if xz.2 = none then (patchLaw X).w xz.1 else 0
  nonneg xz := by
    cases pair <;> cases xz.2 <;> simp [mul_nonneg, (patchLaw X).nonneg]
  sum_one := by
    rw [Fintype.sum_prod_type]
    cases pair
    · simp [Fintype.sum_option, (patchLaw X).sum_one]
    · simp [Fintype.sum_option, ← Finset.mul_sum, (patchLaw X).sum_one]

private theorem patch_expect (F : Fin (T.S.N k) → ℝ) :
    (patchLaw X).E F = (∑ x ∈ (PT.tiling.P (D.geom.patchOf X.target)).X, F x) /
      (PT.tiling.P (D.geom.patchOf X.target)).M := by
  simp only [patchLaw, FinLaw.E, FinLaw.uniform, ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter, (PT.tiling.P _).cardX]
  rw [← Finset.mul_sum]
  ring

theorem expect_eq_mean (pair : Bool)
    (F : Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ) :
    (law X pair).E (fun xz => F xz.1 xz.2) = witnessMean X pair F := by
  cases pair
  · change (∑ xz : Fin (T.S.N k) × Option (Fin (T.S.N k)), (if xz.2 = none then (patchLaw X).w xz.1 else 0) * F xz.1 xz.2) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_option, Option.some_ne_none, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero]
    exact patch_expect _
  · have heq : (law X true).E (fun xz => F xz.1 xz.2) =
        (patchLaw X).E (fun x => (patchLaw X).E (fun z => F x (some z))) := by
      unfold FinLaw.E
      rw [Fintype.sum_prod_type]
      simp only [law, ↓reduceIte, Fintype.sum_option, zero_mul, zero_add]
      simp only [Finset.mul_sum, mul_assoc]
    rw [heq, patch_expect]
    simp_rw [patch_expect, ← Finset.sum_div]
    simp only [witnessMean, ↓reduceIte, div_div, pow_two]

theorem probability_eq_mean (pair : Bool)
    (A : Fin (T.S.N k) → Option (Fin (T.S.N k)) → Prop) :
    (law X pair).pr (fun xz => A xz.1 xz.2) =
      witnessMean X pair (fun x z => if A x z then 1 else 0) := by
  have h := expect_eq_mean (X := X) pair (fun x z => if A x z then 1 else 0)
  simpa only [FinLaw.E, FinLaw.pr, mul_ite, mul_one, mul_zero] using h

/-- Fubini for explicit finite laws, without a transcript cardinality factor. -/
theorem expect_commute {Ω W : Type*} [Fintype Ω] [Fintype W]
    (Q : FinLaw Ω) (τ : FinLaw W) (F : W → Ω → ℝ) :
    τ.E (fun w => Q.E (F w)) = Q.E (fun s => τ.E (fun w => F w s)) := by
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem mean_expect {Ω : Type*} [Fintype Ω] (Q : FinLaw Ω) (pair : Bool)
    (F : Fin (T.S.N k) → Option (Fin (T.S.N k)) → Ω → ℝ) :
    witnessMean X pair (fun x z => Q.E (F x z)) =
      Q.E (fun s => witnessMean X pair (fun x z => F x z s)) := by
  calc
    _ = (law X pair).E (fun xz => Q.E (F xz.1 xz.2)) := (expect_eq_mean pair _).symm
    _ = Q.E (fun s => (law X pair).E (fun xz => F xz.1 xz.2 s)) := expect_commute Q (law X pair) _
    _ = _ := by
      congr 1
      funext s
      exact expect_eq_mean pair (fun x z => F x z s)

theorem mean_sum {I : Type*} (S : Finset I) (pair : Bool)
    (F : I → Fin (T.S.N k) → Option (Fin (T.S.N k)) → ℝ) :
    witnessMean X pair (fun x z => ∑ i ∈ S, F i x z) =
      ∑ i ∈ S, witnessMean X pair (F i) := by
  rw [← expect_eq_mean]
  have heq : (∑ i ∈ S, (law X pair).E (fun xz => F i xz.1 xz.2)) =
      ∑ i ∈ S, witnessMean X pair (F i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact expect_eq_mean pair (F i)
  rw [← heq]
  unfold FinLaw.E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

noncomputable def hit (X : CriticalTransferData D)
    (xz : Fin (T.S.N k) × Option (Fin (T.S.N k))) (y : Fin (T.S.N k)) : Prop :=
  Hits (T.S.E k) PT.tiling.c xz.1 y ∧ ∀ z, xz.2 = some z → Hits (T.S.E k) PT.tiling.c z y

theorem hit_none (x : Fin (T.S.N k)) : hit X (x, none) = Hits (T.S.E k) PT.tiling.c x := by
  funext y
  simp [hit]

theorem hit_some (x z : Fin (T.S.N k)) : hit X (x, some z) =
    (fun y => Hits (T.S.E k) PT.tiling.c x y ∧ Hits (T.S.E k) PT.tiling.c z y) := by
  funext y
  simp [hit]

noncomputable def baseline (pair : Bool) : ℝ := if pair then 1 / 4 else 1 / 2
noncomputable def tolerance (T : Stage) (k : ℕ) (pair : Bool) : ℝ := if pair then 2 * bstar T k else bstar T k

/-- Broad singleton and pair estimates expressed against the same finite
witness law used by the stopped moment and exception definitions. -/
theorem broad_hit_exception (hκ : κ.Admissible)
    (hdisc : TwoBudgetDisc T k (Real.rpow (T.S.n k : ℝ) κ.xs) (κ.α * T.S.n k) (bstar T k))
    (hn : 1 ≤ (T.S.n k : ℝ)) (hslack : Real.log 4 ≤ κ.α * T.S.n k / 2)
    (hb : bstar T k ≤ 1 / 4) (pair : Bool)
    (U : Law (T.S.N k)) (hU : U.SupportedIn (T.Y k)) (hUw : U.WidthLE (κ.α * T.S.n k / 2)) :
    (law X pair).pr (fun xz => tolerance T k pair < |U.pr (hit X xz) - baseline pair|) ≤
      4 * Real.exp (Real.log 400 + (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι -
        Real.rpow (T.S.n k : ℝ) κ.xs) := by
  let i := D.geom.patchOf X.target
  let τ := Law.unif (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
  let w := Real.log 400 + (1 + |κ.a|) * Real.rpow (T.S.n k : ℝ) κ.ι
  have hτ : τ.SupportedIn (T.X k) := by
    intro x hx
    have hnot : x ∉ (PT.tiling.P i).X := by
      intro hm
      exact hx (Finset.mem_sdiff.mp ((hPT.tiling_valid.patch_supports i).2.1
        ((hPT.tiling_valid.patch_supports i).1 hm))).1
    simp [τ, Law.unif, FinProb.uniform, hnot]
  have hτw : τ.WidthLE w := by
    have hh := Law.uniform_width (PT.tiling.P i).X (hPT.tiling_valid.patch_nonempty i).1
    change (Law.unif (PT.tiling.P i).X _).WidthLE _ at hh
    rw [(PT.tiling.P i).cardX] at hh
    exact hh.mono (Lane_sol_fix_outsupp.patch_log_width hκ hPT hn i)
  have hweights : (patchLaw X).w = τ.w := by
    funext x
    simp [patchLaw, τ, i, FinLaw.uniform, Law.unif, FinProb.uniform, one_div]
  cases pair
  · have hh := Cylinder.single_hit_exception PT.tiling.c _ _ _ w hdisc τ U hτ hτw hU hUw
      (show κ.α * T.S.n k / 2 ≤ κ.α * T.S.n k by
        have hαn : 0 ≤ κ.α * (T.S.n k : ℝ) := mul_nonneg hκ.α_rng.1.le (Nat.cast_nonneg _)
        linarith)
    have hprob : (law X false).pr (fun xz => tolerance T k false < |U.pr (hit X xz) - baseline false|) =
        (⟨τ.w, τ.nonneg, τ.sum_eq_one⟩ : FinLaw (Fin (T.S.N k))).pr
          (fun x => bstar T k < |U.pr (Hits (T.S.E k) PT.tiling.c x) - 1 / 2|) := by
      unfold FinLaw.pr
      rw [Fintype.sum_prod_type]
      simp only [law, Bool.false_eq_true, ↓reduceIte, Fintype.sum_option,
        Option.some_ne_none, hit, baseline, tolerance, hweights, zero_add, add_zero]
      simp [hit_none, hit_some]
    rw [hprob]
    exact hh.trans (by
      have he := (Real.exp_pos (w - Real.rpow (T.S.n k : ℝ) κ.xs)).le
      simp only [w, Real.rpow_eq_pow] at he ⊢
      linarith only [he])
  · have hh := Cylinder.pair_hit_exception PT.tiling.c _ _ _ w hdisc τ U hτ hτw hU hUw
      (show κ.α * T.S.n k / 2 + Real.log 4 ≤ κ.α * T.S.n k by linarith) hb
    have hprob : (law X true).pr (fun xz => tolerance T k true < |U.pr (hit X xz) - baseline true|) =
        (FinLaw.bind (⟨τ.w, τ.nonneg, τ.sum_eq_one⟩ : FinLaw (Fin (T.S.N k)))
          (fun _ => ⟨τ.w, τ.nonneg, τ.sum_eq_one⟩)).pr (fun xz => 2 * bstar T k <
            |U.pr (fun y => Hits (T.S.E k) PT.tiling.c xz.1 y ∧ Hits (T.S.E k) PT.tiling.c xz.2 y) - 1 / 4|) := by
      unfold FinLaw.pr FinLaw.bind
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [law, ↓reduceIte, Fintype.sum_option, hit, baseline, tolerance, hweights]
      simp [hit_none, hit_some]
    rw [hprob]
    exact hh

end HypercubeRamsey.S18.Lane_sol_s18_2lm.Witnesses
