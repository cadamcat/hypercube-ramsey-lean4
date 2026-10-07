import HypercubeRamsey.S06.Steps_q_s06_steps1
import HypercubeRamsey.S06.Steps_sol_s06_steps1

namespace HypercubeRamsey.S06.Lane_sol_s06_steps1
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

theorem withTag_twice (b : X.Base) (k : X.Key) (i j : X.ι) :
    X.withTag (X.withTag b k i) k j = X.withTag b k j := by
  simp [Ctx6.withTag, Function.update_idem]

theorem hidPostDel_withTag (b : X.Base) (h k : X.Key) (i : X.ι) :
    X.hidPostDel (X.withTag b k i) h k = X.hidPostDel b h k := by
  unfold Ctx6.hidPostDel
  congr 1
  funext y
  unfold Ctx6.hidWeight
  have hp : X.parOf (X.withTag b k i) = X.parOf b := rfl
  rw [hp]
  dsimp only
  have hprod : (∏ s ∈ (X.C h).erase k,
      (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w
        ((X.withTag b k i).2.2 s)) =
      ∏ s ∈ (X.C h).erase k,
        (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w (b.2.2 s) := by
    apply Finset.prod_congr rfl
    intro s hs
    simp [Ctx6.withTag, (Finset.mem_erase.mp hs).1]
  rw [hprod]
  rfl

theorem hidPostRep_withTag (b : X.Base) (h k : X.Key) (i j : X.ι) :
    X.hidPostRep (X.withTag b k i) h k j = X.hidPostRep b h k j := by
  simp [Ctx6.hidPostRep, withTag_twice]

theorem tagGate_withTag (b : X.Base) (β : X.Ty) (i j : X.ι) :
    X.tagGate (X.withTag b β.key i) β j ↔ X.tagGate b β j := by
  simp only [Ctx6.tagGate, hidPostRep_withTag, hidPostDel_withTag]

theorem tagMass_withTag (b : X.Base) (z : X.Hid) (β : X.Ty) (S : Finset X.HKey) (i : X.ι) :
    X.tagMass (X.withTag b β.key i, z) β S = X.tagMass (b, z) β S := by
  unfold Ctx6.tagMass Ctx6.tagWeight
  simp only [tagGate_withTag, hidPostRep_withTag, hidPostDel_withTag]
  rfl

theorem tagMass_density (b : X.Base) (z : X.Hid) (β : X.Ty) (S : Finset X.HKey) :
    X.tagMass (b,z) β S =
      density (X.tagLawAt (X.parOf b) β.key)
        (fun i ℓ => X.hidPostRep b ℓ.1 β.key i)
        (fun ℓ => X.hidPostDel b ℓ.1 β.key)
        (X.tagGate b β) S z := rfl

/-- The failure estimate with all base coordinates except the tested tag held fixed. -/
theorem step2_conditional_bound (b : X.Base) (β : X.Ty) (hn : 1 ≤ n) :
    (∑ i, (X.tagLawAt (X.parOf b) β.key).w i *
      (X.hidLaw (X.withTag b β.key i)).pr (fun z =>
        X.Step2Fail (X.withTag b β.key i, z) β)) ≤
      ((β.obs.card : ℝ) + 1) * X.step2Thr β := by
  let P := X.tagLawAt (X.parOf b) β.key
  let Q (i : X.ι) (ℓ : X.HKey) := X.hidPostRep b ℓ.1 β.key i
  let R (ℓ : X.HKey) := X.hidPostDel b ℓ.1 β.key
  let gate := X.tagGate b β
  let bad (z : X.Hid) := X.tagMass (b,z) β β.obs < X.step2Thr β ∨
    ∃ ℓ ∈ β.obs, X.tagMass (b,z) β β.obs < X.step2Thr β * X.tagMass (b,z) β (β.obs.erase ℓ)
  have hthr : 0 ≤ X.step2Thr β := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have habs : ∀ i, gate i → ∀ ℓ ∈ β.obs, ∀ y, (R ℓ).w y = 0 → (Q i ℓ).w y = 0 := by
    intro i hi ℓ hℓ y hy
    have h := hi ℓ hℓ y
    change (Q i ℓ).w y ≤ (n : ℝ) ^ d₁ * (R ℓ).w y at h
    rw [hy, mul_zero] at h
    exact le_antisymm h ((Q i ℓ).nonneg y)
  have hbound := gated_tests_bound P Q R gate β.obs (X.step2Thr β) hthr (fun _ => X.y₀) habs
  have hpoint (i : X.ι) :
      (X.hidLaw (X.withTag b β.key i)).pr (fun z =>
        X.Step2Fail (X.withTag b β.key i, z) β) ≤
      (if gate i then (FinProb.pi (Q i)).pr bad else 0) := by
    by_cases hg : gate i
    · rw [if_pos hg]
      apply pr_mono6
      intro z hz
      have h := Lane_q_s06_steps1.notStep2Tests_cases6 X (X.withTag b β.key i,z) β hn hz.2
      simpa only [bad, tagMass_withTag] using h
    · have hzero : (X.hidLaw (X.withTag b β.key i)).pr (fun z =>
          X.Step2Fail (X.withTag b β.key i, z) β) = 0 := by
        apply pr_zero_of_supp6
        intro z _ hz
        have ht : X.tagGate b β i := by
          have hh := hz.1
          have hval : (X.withTag b β.key i).2.2 β.key = i := by simp [Ctx6.withTag]
          rw [hval] at hh
          exact (tagGate_withTag X b β i i).mp hh
        exact hg ht
      simp [hg, hzero]
  calc
    _ ≤ ∑ i, P.w i * (if gate i then (FinProb.pi (Q i)).pr bad else 0) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (P.nonneg i)
    _ ≤ ((β.obs.card : ℝ) + 1) * X.step2Thr β := by
      simpa only [bad, tagMass_density, P, Q, R, gate] using hbound


theorem step2_raw_bound (β : X.Ty) (hn : 1 ≤ n) :
    X.rawHist.pr (fun H => X.Step2Fail H β) ≤
      ((β.obs.card : ℝ) + 1) * X.step2Thr β := by
  let c := ((β.obs.card : ℝ) + 1) * X.step2Thr β
  let f (b : X.Base) := (X.hidLaw b).pr (fun z => X.Step2Fail (b,z) β)
  have htags (v : Fin N) (A : X.Bin → Fin N) :
      (FinProb.pi (X.tagLawAt (v,A))).expect (fun I => f (v,A,I)) ≤ c := by
    rw [pi_expect_split_at _ β.key]
    have hcond (J : {j : X.Key // j ≠ β.key} → X.ι) :
        (∑ i, (X.tagLawAt (v,A) β.key).w i *
          f (v,A,(Equiv.funSplitAt β.key X.ι).symm (i,J))) ≤ c := by
      let b : X.Base := (v,A,(Equiv.funSplitAt β.key X.ι).symm (X.i₀,J))
      have hupdate (i : X.ι) : X.withTag b β.key i =
          (v,A,(Equiv.funSplitAt β.key X.ι).symm (i,J)) := by
        change (v,A,Function.update b.2.2 β.key i) = _
        congr 1
        congr 1
        funext j
        by_cases hj : j = β.key
        · subst j
          simp [Ctx6.withTag, b, Equiv.funSplitAt, Equiv.piSplitAt]
        · simp [Ctx6.withTag, b, Equiv.funSplitAt, Equiv.piSplitAt, hj]
      have h := step2_conditional_bound X b β hn
      simpa only [hupdate, Ctx6.parOf, b, f, c] using h
    calc
      _ ≤ ∑ J, (FinProb.pi (fun j : {j : X.Key // j ≠ β.key} =>
          X.tagLawAt (v,A) j.1)).w J * c :=
        Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hcond J) (FinProb.pi _ |>.nonneg J)
      _ = c := by rw [← Finset.sum_mul, FinProb.sum_eq_one, one_mul]
  have hcoarse (v : Fin N) : (X.coarseLaw v).expect (fun AI => f (v,AI)) ≤ c := by
    change ((FinProb.pi (fun _ : X.Bin => X.candLaw v)).bind
      (fun A => FinProb.pi (X.tagLawAt (v,A)))).expect (fun AI => f (v,AI.1,AI.2)) ≤ c
    rw [FinProb.bind_expect (FinProb.pi (fun _ : X.Bin => X.candLaw v))
      (fun A => FinProb.pi (X.tagLawAt (v,A))) (fun A I => f (v,A,I))]
    calc
      _ ≤ ∑ A, (FinProb.pi (fun _ : X.Bin => X.candLaw v)).w A * c :=
        Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (htags v A) (FinProb.pi _ |>.nonneg A)
      _ = c := by rw [← Finset.sum_mul, FinProb.sum_eq_one, one_mul]
  have hbase : X.baseLaw.expect f ≤ c := by
    change (X.initLaw.bind X.coarseLaw).expect (fun b => f (b.1,b.2)) ≤ c
    rw [FinProb.bind_expect X.initLaw X.coarseLaw (fun v AI => f (v,AI))]
    calc
      _ ≤ ∑ v, X.initLaw.w v * c :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcoarse v) (X.initLaw.nonneg v)
      _ = c := by rw [← Finset.sum_mul, X.initLaw.sum_eq_one, one_mul]
  simpa only [Ctx6.rawHist, pr_bind_eq6, FinProb.expect, f, c] using hbase

/-- The union prefactor is absorbed uniformly in every positive severity. -/
theorem step2_prefactor (hn : 1 ≤ (n : ℝ))
    (hbig : 1206 ≤ (n : ℝ) ^ (δ₂ / 2)) (u : ℕ) (hu : 1 ≤ u) :
    (603 * (u : ℝ)) * (n : ℝ) ^ (-(δ₂ * u)) ≤ (n : ℝ) ^ (-(δ₂ * u / 2)) := by
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hpowNat : ∀ v : ℕ, (603 : ℝ) * ((v+1 : ℕ) : ℝ) ≤ (1206 : ℝ) ^ (v+1) := by
    intro v
    induction v with
    | zero => norm_num
    | succ v hv =>
      rw [pow_succ]
      push_cast at *
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1206 by norm_num) (v+1)]
  have huPow : (603 : ℝ) * (u : ℝ) ≤ (1206 : ℝ) ^ u := by
    obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    exact hpowNat v
  have hpower : (1206 : ℝ) ^ u ≤ (n : ℝ) ^ (δ₂ * u / 2) := by
    calc
      _ ≤ ((n : ℝ) ^ (δ₂ / 2)) ^ u := pow_le_pow_left₀ (by norm_num) hbig u
      _ = (n : ℝ) ^ (δ₂ * u / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnp.le]
        congr 1
        ring
  calc
    _ ≤ (n : ℝ) ^ (δ₂ * u / 2) * (n : ℝ) ^ (-(δ₂ * u)) :=
      mul_le_mul_of_nonneg_right (le_trans huPow hpower) (Real.rpow_nonneg hnp.le _)
    _ = (n : ℝ) ^ (-(δ₂ * u / 2)) := by
      rw [← Real.rpow_add hnp]
      congr 1
      ring

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
