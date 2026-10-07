import HypercubeRamsey.S18.Defs
import HypercubeRamsey.Framework.FinProbLemmas

namespace HypercubeRamsey.Lane_sol_s18_n4

open Classical
open scoped BigOperators

private def asProb {Ω : Type*} [Fintype Ω] (P : FinLaw Ω) : FinProb Ω :=
  ⟨P.w, P.nonneg, P.sum_one⟩

private def asLaw {Ω : Type*} [Fintype Ω] (P : FinProb Ω) : FinLaw Ω :=
  ⟨P.w, P.nonneg, P.sum_eq_one⟩

theorem labelWeightCap
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (j : Fin D.geom.r)
    (b : {v : Pos T k // v ∈ D.encoding.base.classes j})
    (side : D.encoding.base.RowOut b.1) (tests : Finset (Fin (T.S.n k))) (y : Fin (T.S.N k)) :
    D.labelWeight j side tests y ≤
      2 / ((D.encoding.base.latePool j).card : ℝ) * Real.exp ((κ.α / 100) * (T.S.n k : ℝ)) := by
  classical
  have hclass := (D.encoding.base.class_of_spec b.1 j).1 b.2
  have hcard : (D.encoding.base.latePool j).card ≤ 2 * side.1.1.card := by
    simpa only [LateProcessBase.latePoolOf, hclass] using side.1.2.2
  have hpool : 0 < ((D.encoding.base.latePool j).card : ℝ) := by
    exact_mod_cast D.late_pool_pos j
  have hmask : 0 < (side.1.1.card : ℝ) := by
    have hcard' : ((D.encoding.base.latePool j).card : ℝ) ≤ 2 * (side.1.1.card : ℝ) := by
      exact_mod_cast hcard
    linarith
  have hcap : D.maskWeight side y ≤ 2 / ((D.encoding.base.latePool j).card : ℝ) := by
    unfold S18.LateData.maskWeight
    split_ifs
    · apply (div_le_div_iff₀ hmask hpool).2
      have hcard' : ((D.encoding.base.latePool j).card : ℝ) ≤ 2 * (side.1.1.card : ℝ) := by
        exact_mod_cast hcard
      simpa only [one_mul] using hcard'
    · positivity
  have hc0 : 0 ≤ 2 / ((D.encoding.base.latePool j).card : ℝ) := by positivity
  let a : ℝ := (κ.α / 100) * (T.S.n k : ℝ)
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (div_nonneg D.constants.α_rng.1.le (by norm_num)) (Nat.cast_nonneg _)
  have hexp : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  unfold S18.LateData.labelWeight
  simp only [neg_mul]
  change (if Real.exp (-a) ≤ D.retainedMass j side tests then
    if D.passes j side tests y then D.maskWeight side y / D.retainedMass j side tests else 0
    else D.maskWeight side y) ≤ _
  split_ifs with hm hp
  · have hm0 := lt_of_lt_of_le (Real.exp_pos (-a)) hm
    calc
      D.maskWeight side y / D.retainedMass j side tests ≤
          (2 / ((D.encoding.base.latePool j).card : ℝ)) / D.retainedMass j side tests :=
        div_le_div_of_nonneg_right hcap hm0.le
      _ ≤ (2 / ((D.encoding.base.latePool j).card : ℝ)) / Real.exp (-a) :=
        div_le_div_of_nonneg_left hc0 (Real.exp_pos _) hm
      _ = 2 / ((D.encoding.base.latePool j).card : ℝ) * Real.exp a := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
        simp
  · positivity
  · exact le_trans hcap (le_mul_of_one_le_right hc0 hexp)

theorem localComparisonOfCylinders
    {R : Type*} [Fintype R] [DecidableEq R] {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] [∀ a, DecidableEq (Ω a)]
    (p : ∀ a, FinProb (Ω a)) (J : FinProb (∀ a, Ω a)) (S : Finset R)
    (o₀ : ∀ a, Ω a) (c : ℝ)
    (hcyl : ∀ o : (∀ a, Ω a), J.pr (fun ω => ∀ a ∈ S, ω a = o a) ≤ c * ∏ a ∈ S, (p a).w (o a))
    (Ψ : (∀ a, Ω a) → ℝ) (hΨ : ∀ ω, 0 ≤ Ψ ω)
    (hdep : DependsOn Ψ (S : Set R)) :
    J.expect Ψ ≤ c * (FinProb.pi p).expect Ψ := by
  classical
  let extend := fun o : (∀ a : S, Ω a.1) =>
    fun a => if ha : a ∈ S then o ⟨a, ha⟩ else o₀ a
  let proj := fun ω : (∀ a, Ω a) => fun a : S => ω a.1
  have hvalue : ∀ ω, Ψ ω = Ψ (extend (proj ω)) := by
    intro ω
    apply hdep
    intro a ha
    change a ∈ S at ha
    simp [extend, proj, ha]
  have hweight : ∀ o, (FinProb.map J proj).w o ≤
      c * (FinProb.pi (fun a : S => p a.1)).w o := by
    intro o
    have hevent : (fun ω => proj ω = o) = (fun ω => ∀ a ∈ S, ω a = extend o a) := by
      funext ω
      apply propext
      constructor
      · intro heq a ha
        have h := congrFun heq ⟨a, ha⟩
        simpa [proj, extend, ha] using h
      · intro heq
        funext a
        simpa [proj, extend, a.2] using heq a.1 a.2
    have hprod : (∏ a ∈ S, (p a).w (extend o a)) =
        (FinProb.pi (fun a : S => p a.1)).w o := by
      rw [FinProb.pi, ← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro a ha
      simp [extend, a.2]
    have hm : (FinProb.map J proj).w o = J.pr (fun ω => proj ω = o) := by
      unfold FinProb.map FinProb.pr
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : proj ω = o <;> simp [h]
    rw [hm]
    rw [hevent, ← hprod]
    exact hcyl (extend o)
  have hJ : J.expect Ψ = (FinProb.map J proj).expect (fun o => Ψ (extend o)) := by
    rw [FinProb.map_expect]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro ω hω
    exact congrArg (fun t => J.w ω * t) (hvalue ω)
  have hP : (FinProb.pi p).expect Ψ =
      (FinProb.pi (fun a : S => p a.1)).expect (fun o => Ψ (extend o)) := by
    calc
      (FinProb.pi p).expect Ψ = (FinProb.pi p).expect (fun ω => Ψ (extend (proj ω))) := by
        congr 1
        exact funext hvalue
      _ = _ := FinProb.pi_marginal_expect p S (fun o => Ψ (extend o))
  rw [hJ, hP]
  unfold FinProb.expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro o ho
  calc
    (FinProb.map J proj).w o * Ψ (extend o) ≤
        (c * (FinProb.pi (fun a : S => p a.1)).w o) * Ψ (extend o) :=
      mul_le_mul_of_nonneg_right (hweight o) (hΨ _)
    _ = c * ((FinProb.pi (fun a : S => p a.1)).w o * Ψ (extend o)) := by ring

theorem supportOfSingletonComparison
    {R : Type*} [Fintype R] [DecidableEq R] {Ω : R → Type*}
    [∀ a, Fintype (Ω a)] (p : ∀ a, FinLaw (Ω a)) (J : FinLaw (∀ a, Ω a))
    (c : ℝ)
    (hcomp : ∀ a (o : ∀ a, Ω a), J.pr (fun ω => ω a = o a) ≤ c * (p a).w (o a)) :
    ∀ o, J.w o ≠ 0 → (FinLaw.pi p).w o ≠ 0 := by
  classical
  intro o ho
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha hzero
  have hupper := hcomp a o
  rw [hzero, mul_zero] at hupper
  have hlower : J.w o ≤ J.pr (fun ω => ω a = o a) := by
    unfold FinLaw.pr
    simpa using Finset.single_le_sum
      (f := fun ω => if ω a = o a then J.w ω else 0)
      (fun ω _ => by split_ifs <;> simp [J.nonneg]) (Finset.mem_univ o)
  have hnonneg := J.nonneg o
  exact ho (by linarith)

theorem classSamplerOfEnteringLaws
    {κ : CConsts} {T : Stage} {k : ℕ} {PT : ProfiledTiling κ T k}
    {hPT : PT.Valid} (D : S18.LateData hPT) (δ : ℝ) (hn : 1 ≤ T.S.n k)
    (hclock : ∀ j h, D.enter δ j h →
      ∃ J : FinProb (D.encoding.base.ClassRows j),
        (∀ out, J.w out ≠ 0 →
          Function.Injective (fun b => D.encoding.base.rowLabel (out b)) ∧
            out ∉ D.bad j h ∧ out ∉ D.alarm δ j h) ∧
        (∀ (S : Finset {x : Pos T k // x ∈ D.encoding.base.classes j})
          (out : D.encoding.base.ClassRows j),
          (S.card : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) →
          J.pr (fun ω => ∀ b ∈ S, ω b = out b) ≤
            2 * ∏ b ∈ S, (D.encoding.kernels.refK j b h).w (out b))) :
    Nonempty (S18.ClassSamplerData D δ) := by
  classical
  let chosen := fun j h (he : D.enter δ j h) => (hclock j h he).choose
  let act := fun j h => if he : D.enter δ j h then asLaw (chosen j h he)
    else D.encoding.kernels.referenceTransition j h
  have hsingleCard : (1 : ℝ) ≤ Real.exp (Real.log (T.S.n k) ^ 3) := by
    apply Real.one_le_exp_iff.mpr
    exact pow_nonneg (Real.log_nonneg (by exact_mod_cast hn)) _
  refine ⟨⟨act, ?_, ?_⟩⟩
  · intro j h he
    have hJ := (hclock j h he).choose_spec
    simp only [act, dif_pos he]
    refine ⟨hJ.1, ?_⟩
    intro S hS Ψ hΨ hdep
    let ref := D.encoding.kernels.referenceTransition j h
    have hne : Nonempty (D.encoding.base.ClassRows j) := by
      by_contra hnone
      haveI : IsEmpty (D.encoding.base.ClassRows j) := not_nonempty_iff.mp hnone
      have hsum := ref.sum_one
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      norm_num at hsum
    let o₀ := Classical.choice hne
    exact localComparisonOfCylinders
      (fun b => asProb (D.encoding.kernels.refK j b h)) (chosen j h he) S o₀ 2
      (fun out => hJ.2 S out hS) Ψ hΨ hdep
  · intro j h out he hout
    have hJ := (hclock j h he).choose_spec
    have hout' : (asLaw (chosen j h he)).w out ≠ 0 := by
      simpa only [act, dif_pos he] using hout
    apply supportOfSingletonComparison
      (fun b => D.encoding.kernels.refK j b h) (asLaw (chosen j h he)) 2 ?_ out hout'
    intro b o
    change (chosen j h he).pr (fun ω => ω b = o b) ≤ _
    simpa only [Finset.mem_singleton, forall_eq, Finset.prod_singleton] using
      hJ.2 {b} o (by simpa using hsingleCard)

end HypercubeRamsey.Lane_sol_s18_n4
