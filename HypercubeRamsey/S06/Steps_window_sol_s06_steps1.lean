import HypercubeRamsey.S06.Steps_local_sol_s06_steps1

namespace HypercubeRamsey.S06.Lane_sol_s06_steps1
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000
variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

def candWindow (h : X.Key) (v : Fin N) : FinProb (X.Bin → Fin N) :=
  FinProb.pi fun u => if u ∈ X.binsOf (X.C h) then X.candLaw v else pointMass6 X.y₀

def tagWindow (pv : Par6 X.Bin N) (S : Finset X.Key) : FinProb (X.Key → X.ι) :=
  FinProb.pi fun s => if s ∈ S then X.tagLawAt pv s else pointMass6 X.i₀

def baseWindow (h : X.Key) : FinProb X.Base :=
  X.initLaw.bind fun v => (candWindow X h v).bind fun A => tagWindow X (v,A) (X.C h)

theorem base_expect_window (h : X.Key) (F : X.Base → ℝ)
    (hF : ∀ (v : Fin N) (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι),
      (∀ u ∈ X.binsOf (X.C h), A u = A' u) → (∀ s ∈ X.C h, I s = I' s) →
      F (v,A,I) = F (v,A',I')) :
    X.baseLaw.expect F = (baseWindow X h).expect F := by
  let g (v : Fin N) (A : X.Bin → Fin N) :=
    (tagWindow X (v,A) (X.C h)).expect (fun I => F (v,A,I))
  have ht (v : Fin N) (A : X.Bin → Fin N) :
      (FinProb.pi (X.tagLawAt (v,A))).expect (fun I => F (v,A,I)) = g v A := by
    apply pi_expect_congr_on (X.tagLawAt (v,A)) _ (X.C h) _ (fun _ => X.i₀)
    · intro I I' hI
      exact hF v A A I I' (fun _ _ => rfl) hI
    · intro s hs
      simp [hs]
  have hg (v : Fin N) : FinProb.DependsOn (g v) (X.binsOf (X.C h)) := by
    intro A A' hA
    have hp : tagWindow X (v,A) (X.C h) = tagWindow X (v,A') (X.C h) := by
      unfold tagWindow
      congr 1
      funext s
      by_cases hs : s ∈ X.C h
      · simp only [hs, ite_true]
        exact Lane_q_s06_steps1.tagLawAt_eq_of_local_boundary6 X h s hs v A A' hA
      · simp [hs]
    unfold g
    rw [hp]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro I _
    congr 1
    exact hF v A A' I I hA (fun _ _ => rfl)
  have hc (v : Fin N) : (FinProb.pi (fun _ : X.Bin => X.candLaw v)).expect (g v) =
      (candWindow X h v).expect (g v) := by
    apply pi_expect_congr_on _ _ (X.binsOf (X.C h)) _ (fun _ => X.y₀) (hg v)
    intro u hu
    simp [hu]
  change (X.initLaw.bind X.coarseLaw).expect (fun b => F (b.1,b.2)) =
    (X.initLaw.bind (fun v => (candWindow X h v).bind fun A => tagWindow X (v,A) (X.C h))).expect
      (fun b => F (b.1,b.2))
  rw [FinProb.bind_expect X.initLaw _ (fun v AI => F (v,AI)),
    FinProb.bind_expect X.initLaw _ (fun v AI => F (v,AI))]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  change ((FinProb.pi (fun _ : X.Bin => X.candLaw v)).bind
    (fun A => FinProb.pi (X.tagLawAt (v,A)))).expect (fun AI => F (v,AI.1,AI.2)) = _
  rw [FinProb.bind_expect _ _ (fun A I => F (v,A,I)),
    FinProb.bind_expect _ _ (fun A I => F (v,A,I))]
  simp_rw [ht]
  exact hc v

theorem candWindow_weight (h : X.Key) (v : Fin N) (A : X.Bin → Fin N)
    (hA : ∀ u, u ∉ X.binsOf (X.C h) → A u = X.y₀) :
    (candWindow X h v).w A = ∏ u ∈ X.binsOf (X.C h), (X.candLaw v).w (A u) := by
  rw [← Fintype.prod_ite_mem (X.binsOf (X.C h))]
  unfold candWindow
  change (∏ u, (if u ∈ X.binsOf (X.C h) then X.candLaw v else pointMass6 X.y₀).w (A u)) = _
  apply Finset.prod_congr rfl
  intro u _
  by_cases hu : u ∈ X.binsOf (X.C h)
  · simp [hu]
  · simp [hu, pointMass6, hA u hu]

theorem tagWindow_weight (pv : Par6 X.Bin N) (S : Finset X.Key) (I : X.Key → X.ι)
    (hI : ∀ s, s ∉ S → I s = X.i₀) :
    (tagWindow X pv S).w I = ∏ s ∈ S, (X.tagLawAt pv s).w (I s) := by
  rw [← Fintype.prod_ite_mem S]
  unfold tagWindow
  change (∏ s, (if s ∈ S then X.tagLawAt pv s else pointMass6 X.i₀).w (I s)) = _
  apply Finset.prod_congr rfl
  intro s _
  by_cases hs : s ∈ S
  · simp [hs]
  · simp [hs, pointMass6, hI s hs]

theorem candWindow_supported (h : X.Key) (v : Fin N) (A : X.Bin → Fin N)
    (ha : (candWindow X h v).w A ≠ 0) :
    ∀ u, u ∉ X.binsOf (X.C h) → A u = X.y₀ := by
  intro u hu
  by_contra hne
  have hz : (candWindow X h v).w A = 0 := by
    unfold candWindow
    change (∏ u, (if u ∈ X.binsOf (X.C h) then X.candLaw v else pointMass6 X.y₀).w (A u)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ u)
    simp [hu, pointMass6, hne]
  exact ha hz

theorem tagWindow_supported (pv : Par6 X.Bin N) (S : Finset X.Key) (I : X.Key → X.ι)
    (hi : (tagWindow X pv S).w I ≠ 0) : ∀ s, s ∉ S → I s = X.i₀ := by
  intro s hs
  by_contra hne
  have hz : (tagWindow X pv S).w I = 0 := by
    unfold tagWindow
    change (∏ s, (if s ∈ S then X.tagLawAt pv s else pointMass6 X.i₀).w (I s)) = 0
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [hs, pointMass6, hne]
  exact hi hz


theorem tagWindow_resample (pv : Par6 X.Bin N) (S : Finset X.Key) (s : X.Key)
    (hs : s ∈ S) (F : (X.Key → X.ι) → ℝ) :
    (tagWindow X pv S).expect F =
      (tagWindow X pv (S.erase s)).expect
        (fun I => (X.tagLawAt pv s).expect (fun i => F (Function.update I s i))) := by
  unfold tagWindow
  rw [pi_expect_resample _ s X.i₀]
  have hp : (if s ∈ S then X.tagLawAt pv s else pointMass6 X.i₀) = X.tagLawAt pv s := by simp [hs]
  rw [hp]
  have hr : FinProb.pi (fun j => if j = s then pointMass6 X.i₀ else
      if j ∈ S then X.tagLawAt pv j else pointMass6 X.i₀) =
      FinProb.pi (fun j => if j ∈ S.erase s then X.tagLawAt pv j else pointMass6 X.i₀) := by
    congr 1
    funext j
    by_cases hj : j = s <;> simp [hj]
  rw [hr]

/-- The raw deletion alarm for a boundary parent, after retaining its finite candidate window. -/
theorem boundary_alarm_bound (h s : X.Key) (hf : h.2 = .boundary) (hs : s ∈ X.C h)
    (a : ℝ) (ha : 0 ≤ a) :
    X.baseLaw.pr (fun b => posteriorPred X b h s < a * M.Λ (b.2.2 s)) ≤ a := by
  let O (y : Fin N) : FinProb X.Coarse :=
    (candWindow X h y).bind fun A => tagWindow X (y,A) ((X.C h).erase s)
  let P (y : Fin N) (d : X.Coarse) := X.tagLawAt (y,d.1) s
  let B (y : Fin N) (d : X.Coarse) (i : X.ι) :=
    posteriorPred X (y,d.1,Function.update d.2 s i) h s < a * M.Λ i
  have hB : ∀ y d i, X.initLaw.w y * (O y).w d ≠ 0 → B y d i →
      (∑ z, (normalize6 (fun z => X.initLaw.w z * (O z).w d) X.y₀).w z * (P z d).w i) <
        a * (tagLaw6 M).w i := by
    intro y d i hw hb
    have ho : (O y).w d ≠ 0 := right_ne_zero_of_mul hw
    have hc : (candWindow X h y).w d.1 ≠ 0 := left_ne_zero_of_mul ho
    have ht : (tagWindow X (y,d.1) ((X.C h).erase s)).w d.2 ≠ 0 := right_ne_zero_of_mul ho
    have hcfix := candWindow_supported X h y d.1 hc
    have htfix := tagWindow_supported X (y,d.1) ((X.C h).erase s) d.2 ht
    let b : X.Base := (X.y₀,d)
    have hweights : (fun z => X.initLaw.w z * (O z).w d) =
        X.hidWeight b h ((X.C h).erase s) := by
      funext z
      change X.initLaw.w z * ((candWindow X h z).w d.1 *
        (tagWindow X (z,d.1) ((X.C h).erase s)).w d.2) = _
      rw [candWindow_weight X h z d.1 hcfix, tagWindow_weight X (z,d.1) _ d.2 htfix]
      simp [Ctx6.hidWeight, Ctx6.parOf, b, primaryName6, hf, Par6.set, mul_assoc]
    have hpost : normalize6 (fun z => X.initLaw.w z * (O z).w d) X.y₀ =
        X.hidPostDel b h s := by rw [hweights]; rfl
    have heq : posteriorPred X (y,d.1,Function.update d.2 s i) h s =
        posteriorPred X (X.withTag b s i) h s := by
      apply posteriorPred_local X h s hs
      · simp [hf]
      · intro _ u _
        rfl
      · intro t _
        rfl
    have hpred : posteriorPred X (X.withTag b s i) h s =
        ∑ z, (normalize6 (fun z => X.initLaw.w z * (O z).w d) X.y₀).w z * (P z d).w i := by
      rw [hpost]
      unfold posteriorPred
      rw [hidPostDel_withTag]
      apply Finset.sum_congr rfl
      intro z _
      simp [Ctx6.withTag, Ctx6.parOf, primaryName6, hf, Par6.set, b, P]
    have hb' := hb
    change posteriorPred X (y,d.1,Function.update d.2 s i) h s < a * M.Λ i at hb'
    rw [heq, hpred] at hb'
    exact hb'
  have hbound := bayes_experiment_bound X.initLaw O P (tagLaw6 M) B X.y₀ a ha hB
  let F (b : X.Base) : ℝ := if posteriorPred X b h s < a * M.Λ (b.2.2 s) then 1 else 0
  have hF : ∀ (v : Fin N) (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι),
      (∀ u ∈ X.binsOf (X.C h), A u = A' u) → (∀ t ∈ X.C h, I t = I' t) →
      F (v,A,I) = F (v,A',I') := by
    intro v A A' I I' hA hI
    have hp := posteriorPred_local X h s hs (v,A,I) (v,A',I') (fun _ => rfl) (fun _ => hA) hI
    unfold F
    dsimp only
    simp only [hp, hI s hs]
  have hraw : X.baseLaw.pr (fun b => posteriorPred X b h s < a * M.Λ (b.2.2 s)) =
      ∑ y, X.initLaw.w y * (∑ d, (O y).w d * (P y d).pr (B y d)) := by
    have hrepr : X.baseLaw.pr (fun b => posteriorPred X b h s < a * M.Λ (b.2.2 s)) =
        X.baseLaw.expect F := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro b _
      simp [F, mul_ite]
    rw [hrepr, base_expect_window X h F hF]
    change (X.initLaw.bind (fun y => (candWindow X h y).bind fun A => tagWindow X (y,A) (X.C h))).expect
      (fun b => F (b.1,b.2)) = _
    rw [FinProb.bind_expect _ _ (fun y d => F (y,d))]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    change ((candWindow X h y).bind (fun A => tagWindow X (y,A) (X.C h))).expect
      (fun d => F (y,d.1,d.2)) = (O y).expect (fun d => (P y d).pr (B y d))
    rw [FinProb.bind_expect _ _ (fun A I => F (y,A,I)),
      FinProb.bind_expect _ _ (fun A I => (P y (A,I)).pr (B y (A,I)))]
    apply Finset.sum_congr rfl
    intro A _
    congr 1
    rw [tagWindow_resample X (y,A) (X.C h) s hs]
    unfold FinProb.expect FinProb.pr
    apply Finset.sum_congr rfl
    intro I _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hb : B y (A,I) i <;> simp [F, B, P, hb]
  rw [hraw]
  exact hbound


/-- The corresponding deletion alarm with the initial parent held fixed. -/
theorem interior_alarm_bound (h s : X.Key) (hf : h.2 = .interior) (hs : s ∈ X.C h)
    (a : ℝ) (ha : 0 ≤ a) :
    X.baseLaw.pr (fun b => posteriorPred X b h s < a * M.Λ (b.2.2 s)) ≤ a := by
  let A₀ : X.Bin → Fin N := fun _ => X.y₀
  let F (b : X.Base) : ℝ := if posteriorPred X b h s < a * M.Λ (b.2.2 s) then 1 else 0
  have hFsame (v : Fin N) (A A' : X.Bin → Fin N) (I : X.Key → X.ι) : F (v,A,I) = F (v,A',I) := by
    have hp := posteriorPred_local X h s hs (v,A,I) (v,A',I) (fun _ => rfl) (by simp [hf]) (fun _ _ => rfl)
    unfold F
    rw [hp]
  have hFlocal : ∀ (v : Fin N) (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι),
      (∀ u ∈ X.binsOf (X.C h), A u = A' u) → (∀ t ∈ X.C h, I t = I' t) → F (v,A,I) = F (v,A',I') := by
    intro v A A' I I' _ hI
    have hp := posteriorPred_local X h s hs (v,A,I) (v,A',I') (fun _ => rfl) (by simp [hf]) hI
    unfold F
    dsimp only
    simp only [hp, hI s hs]
  let g (v : Fin N) (A : X.Bin → Fin N) := (tagWindow X (v,A) (X.C h)).expect (fun I => F (v,A,I))
  have hg (v : Fin N) : FinProb.DependsOn (g v) {h.1} := by
    intro A A' hA
    have hAA : A h.1 = A' h.1 := hA h.1 (Finset.mem_singleton_self _)
    have hlaw : tagWindow X (v,A) (X.C h) = tagWindow X (v,A') (X.C h) := by
      unfold tagWindow
      congr 1
      funext t
      by_cases ht : t ∈ X.C h
      · simp only [ht, ite_true]
        exact Lane_q_s06_steps1.tagLawAt_eq_of_local_interior6 X h t ht hf v A A' hAA
      · simp [ht]
    unfold g
    rw [hlaw]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro I _
    dsimp only
    rw [hFsame v A A' I]
  have hself : h ∈ X.C h := by simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
  have hbin : h.1 ∈ X.binsOf (X.C h) := Finset.mem_image.mpr ⟨h,hself,rfl⟩
  have hcond (v : Fin N) : (candWindow X h v).expect (g v) ≤ a := by
    let pv (y : Fin N) : Par6 X.Bin N := (v,Function.update A₀ h.1 y)
    let O (y : Fin N) := tagWindow X (pv y) ((X.C h).erase s)
    let P (y : Fin N) (_I : X.Key → X.ι) := X.tagLawAt (pv y) s
    let B (_y : Fin N) (I : X.Key → X.ι) (i : X.ι) :=
      posteriorPred X (v,A₀,Function.update I s i) h s < a * M.Λ i
    have hB : ∀ y I i, (X.candLaw v).w y * (O y).w I ≠ 0 → B y I i →
        (∑ z, (normalize6 (fun z => (X.candLaw v).w z * (O z).w I) X.y₀).w z * (P z I).w i) <
          a * (tagLaw6 M).w i := by
      intro y I i hw hb
      have ht : (O y).w I ≠ 0 := right_ne_zero_of_mul hw
      have htfix := tagWindow_supported X (pv y) ((X.C h).erase s) I ht
      let b : X.Base := (v,A₀,I)
      have hweights : (fun z => (X.candLaw v).w z * (O z).w I) = X.hidWeight b h ((X.C h).erase s) := by
        funext z
        change (X.candLaw v).w z * (tagWindow X (pv z) ((X.C h).erase s)).w I = _
        rw [tagWindow_weight X (pv z) _ I htfix]
        simp [Ctx6.hidWeight, Ctx6.parOf, b, pv, primaryName6, hf, Par6.set]
      have hpost : normalize6 (fun z => (X.candLaw v).w z * (O z).w I) X.y₀ = X.hidPostDel b h s := by
        rw [hweights]
        rfl
      have hpred : posteriorPred X (v,A₀,Function.update I s i) h s =
          ∑ z, (normalize6 (fun z => (X.candLaw v).w z * (O z).w I) X.y₀).w z * (P z I).w i := by
        change posteriorPred X (X.withTag b s i) h s = _
        rw [hpost]
        unfold posteriorPred
        rw [hidPostDel_withTag]
        apply Finset.sum_congr rfl
        intro z _
        simp [Ctx6.withTag, Ctx6.parOf, primaryName6, hf, Par6.set, b, P, pv]
      change posteriorPred X (v,A₀,Function.update I s i) h s < a * M.Λ i at hb
      rw [hpred] at hb
      exact hb
    have hbound := bayes_experiment_bound (X.candLaw v) O P (tagLaw6 M) B X.y₀ a ha hB
    have heq : (candWindow X h v).expect (g v) =
        ∑ y, (X.candLaw v).w y * (∑ I, (O y).w I * (P y I).pr (B y I)) := by
      unfold candWindow
      rw [pi_expect_single _ h.1 A₀ (g v) (hg v)]
      change (if h.1 ∈ X.binsOf (X.C h) then X.candLaw v else pointMass6 X.y₀).expect
        (fun y => g v (Function.update A₀ h.1 y)) = _
      rw [if_pos hbin]
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      change (tagWindow X (pv y) (X.C h)).expect (fun I => F (v,Function.update A₀ h.1 y,I)) = _
      rw [tagWindow_resample X (pv y) (X.C h) s hs]
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro I _
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      dsimp only
      rw [hFsame v (Function.update A₀ h.1 y) A₀ (Function.update I s i)]
      by_cases hb : B y I i <;> simp [F, B, P, pv, hb]
    rw [heq]
    exact hbound
  have hrepr : X.baseLaw.pr (fun b => posteriorPred X b h s < a * M.Λ (b.2.2 s)) = X.baseLaw.expect F := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro b _
    simp [F, mul_ite]
  rw [hrepr, base_expect_window X h F hFlocal]
  change (X.initLaw.bind (fun v => (candWindow X h v).bind fun A => tagWindow X (v,A) (X.C h))).expect
    (fun b => F (b.1,b.2)) ≤ a
  rw [FinProb.bind_expect _ _ (fun v d => F (v,d))]
  calc
    _ = ∑ v, X.initLaw.w v * (candWindow X h v).expect (g v) := by
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      exact FinProb.bind_expect _ _ (fun A I => F (v,A,I))
    _ ≤ ∑ v, X.initLaw.w v * a :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hcond v) (X.initLaw.nonneg v)
    _ = a := by rw [← Finset.sum_mul, X.initLaw.sum_eq_one, one_mul]

theorem posterior_alarm_bound (h s : X.Key) (hs : s ∈ X.C h) (a : ℝ) (ha : 0 ≤ a) :
    X.baseLaw.pr (fun b => posteriorPred X b h s < a * M.Λ (b.2.2 s)) ≤ a := by
  cases hf : h.2
  · exact interior_alarm_bound X h s hf hs a ha
  · exact boundary_alarm_bound X h s hf hs a ha

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
