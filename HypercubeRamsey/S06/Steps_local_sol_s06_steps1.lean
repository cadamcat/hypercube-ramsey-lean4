import HypercubeRamsey.S06.Steps_raw_sol_s06_steps1
import HypercubeRamsey.S06.Steps_bayes_sol_s06_steps1

namespace HypercubeRamsey.S06.Lane_sol_s06_steps1
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section

def fill {I Ω : Type*} [DecidableEq I] (S : Finset I)
    (x : {i : I // i ∈ S} → Ω) (z₀ : I → Ω) : I → Ω :=
  fun i => if hi : i ∈ S then x ⟨i,hi⟩ else z₀ i

@[simp] theorem fill_mem {I Ω : Type*} [DecidableEq I] (S : Finset I)
    (x : {i : I // i ∈ S} → Ω) (z₀ : I → Ω) (i : {i : I // i ∈ S}) :
    fill S x z₀ i.1 = x i := by simp [fill, i.property]

theorem pi_expect_fill {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (S : Finset I) (f : (I → Ω) → ℝ) (z₀ : I → Ω)
    (hf : FinProb.DependsOn f S) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun i : {i : I // i ∈ S} => P i.1)).expect
        (fun x => f (fill S x z₀)) := by
  rw [FinProb.pi_expect_depends P S f z₀ hf]
  rfl


/-- Redrawing one coordinate is equivalent to freezing it and integrating its original law. -/
theorem pi_expect_resample {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (k : I) (z₀ : Ω) (f : (I → Ω) → ℝ) :
    (FinProb.pi P).expect f =
      (FinProb.pi (fun j => if j = k then pointMass6 z₀ else P j)).expect
        (fun z => (P k).expect (fun i => f (Function.update z k i))) := by
  let e := Equiv.funSplitAt k Ω
  let R (j : I) := if j = k then pointMass6 z₀ else P j
  have hupdate (a : Ω) (J : {j : I // j ≠ k} → Ω) (i : Ω) :
      Function.update (e.symm (a,J)) k i = e.symm (i,J) := by
    funext j
    by_cases hj : j = k
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hR : FinProb.pi (fun j : {j : I // j ≠ k} => R j.1) =
      FinProb.pi (fun j : {j : I // j ≠ k} => P j.1) := by
    congr 1
    funext j
    simp [R, j.property]
  rw [pi_expect_split_at P k, pi_expect_split_at R k]
  apply Finset.sum_congr rfl
  intro J _
  rw [hR]
  congr 1
  simp only [R, ite_true, pointMass6, FinProb.expect]
  simp
  apply Finset.sum_congr rfl
  intro i _
  rw [hupdate]

theorem pi_expect_single {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (k : I) (z₀ : I → Ω) (f : (I → Ω) → ℝ)
    (hf : FinProb.DependsOn f {k}) :
    (FinProb.pi P).expect f = (P k).expect (fun y => f (Function.update z₀ k y)) := by
  rw [pi_expect_split_at P k]
  have heq (y : Ω) (J : {j : I // j ≠ k} → Ω) :
      f ((Equiv.funSplitAt k Ω).symm (y,J)) = f (Function.update z₀ k y) := by
    apply hf
    intro j hj
    have hj' : j = k := Finset.mem_singleton.mp hj
    subst j
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  simp_rw [heq]
  rw [← Finset.sum_mul, FinProb.sum_eq_one, one_mul]
  rfl

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- Marginalize the candidates and tags outside the finite posterior window. -/
theorem base_expect_local (h : X.Key) (F : X.Base → ℝ)
    (hF : ∀ (v : Fin N) (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι),
      (∀ u ∈ X.binsOf (X.C h), A u = A' u) → (∀ s ∈ X.C h, I s = I' s) →
      F (v,A,I) = F (v,A',I')) :
    X.baseLaw.expect F = ∑ v, X.initLaw.w v *
      (FinProb.pi (fun u : {u : X.Bin // u ∈ X.binsOf (X.C h)} => X.candLaw v)).expect
        (fun A =>
          (FinProb.pi (fun s : {s : X.Key // s ∈ X.C h} =>
            X.tagLawAt (v,fill (X.binsOf (X.C h)) A (fun _ => X.y₀)) s.1)).expect
              (fun I => F (v,fill (X.binsOf (X.C h)) A (fun _ => X.y₀),
                fill (X.C h) I (fun _ => X.i₀)))) := by
  let S := X.binsOf (X.C h)
  let T := X.C h
  let inner (v : Fin N) (A : X.Bin → Fin N) :=
    (FinProb.pi (fun s : {s : X.Key // s ∈ T} => X.tagLawAt (v,A) s.1)).expect
      (fun I => F (v,A,fill T I (fun _ => X.i₀)))
  have htag (v : Fin N) (A : X.Bin → Fin N) :
      (FinProb.pi (X.tagLawAt (v,A))).expect (fun I => F (v,A,I)) = inner v A := by
    apply pi_expect_fill
    intro I I' hI
    exact hF v A A I I' (fun _ _ => rfl) hI
  have hdep (v : Fin N) : FinProb.DependsOn (inner v) S := by
    intro A A' hA
    have hlaw : FinProb.pi (fun s : {s : X.Key // s ∈ T} => X.tagLawAt (v,A) s.1) =
        FinProb.pi (fun s : {s : X.Key // s ∈ T} => X.tagLawAt (v,A') s.1) := by
      congr 1
      funext s
      exact Lane_q_s06_steps1.tagLawAt_eq_of_local_boundary6 X h s.1 s.2 v A A' hA
    unfold inner
    rw [hlaw]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro I _
    congr 1
    exact hF v A A' _ _ hA (fun _ _ => rfl)
  change (X.initLaw.bind X.coarseLaw).expect (fun b => F (b.1,b.2)) = _
  rw [FinProb.bind_expect X.initLaw X.coarseLaw (fun v AI => F (v,AI))]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  change ((FinProb.pi (fun _ : X.Bin => X.candLaw v)).bind
    (fun A => FinProb.pi (X.tagLawAt (v,A)))).expect (fun AI => F (v,AI.1,AI.2)) = _
  rw [FinProb.bind_expect _ _ (fun A I => F (v,A,I))]
  simp_rw [htag]
  exact pi_expect_fill (fun _ : X.Bin => X.candLaw v) S (inner v) (fun _ => X.y₀) (hdep v)


/-- Posterior weights use their listed tags and the named local parent observations. -/
theorem hidWeight_local (h : X.Key) (obs : Finset X.Key) (hobs : obs ⊆ X.C h)
    (b b' : X.Base) (hv : h.2 = .interior → b.1 = b'.1)
    (hA : h.2 = .boundary → ∀ u ∈ X.binsOf (X.C h), b.2.1 u = b'.2.1 u)
    (hI : ∀ s ∈ obs, b.2.2 s = b'.2.2 s) (y : Fin N) :
    X.hidWeight b h obs y = X.hidWeight b' h obs y := by
  cases hf : h.2
  · have hv' := hv hf
    have hp : (X.parOf b).set (primaryName6 h) y =
        (b.1,Function.update b.2.1 h.1 y) := by simp [Ctx6.parOf, primaryName6, Par6.set, hf]
    have hp' : (X.parOf b').set (primaryName6 h) y =
        (b'.1,Function.update b'.2.1 h.1 y) := by simp [Ctx6.parOf, primaryName6, Par6.set, hf]
    simp only [Ctx6.hidWeight, hf]
    rw [hp, hp', hv']
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    have hlaw := Lane_q_s06_steps1.tagLawAt_eq_of_local_interior6 X h s (hobs hs) hf b'.1
      (Function.update b.2.1 h.1 y) (Function.update b'.2.1 h.1 y) (by simp)
    rw [hlaw, hI s hs]
  · have hA' := hA hf
    have hp : (X.parOf b).set (primaryName6 h) y = (y,b.2.1) := by
      simp [Ctx6.parOf, primaryName6, Par6.set, hf]
    have hp' : (X.parOf b').set (primaryName6 h) y = (y,b'.2.1) := by
      simp [Ctx6.parOf, primaryName6, Par6.set, hf]
    simp only [Ctx6.hidWeight, hf]
    rw [hp, hp']
    have hc : (∏ u ∈ X.binsOf (X.C h), (X.candLaw y).w (b.2.1 u)) =
        ∏ u ∈ X.binsOf (X.C h), (X.candLaw y).w (b'.2.1 u) := by
      apply Finset.prod_congr rfl
      intro u hu
      rw [hA' u hu]
    rw [hc]
    congr 1
    apply Finset.prod_congr rfl
    intro s hs
    have hlaw := Lane_q_s06_steps1.tagLawAt_eq_of_local_boundary6 X h s (hobs hs) y b.2.1 b'.2.1 hA'
    rw [hlaw, hI s hs]

def posteriorPred (b : X.Base) (h s : X.Key) : ℝ :=
  ∑ y, (X.hidPostDel b h s).w y *
    (X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s).w (b.2.2 s)

/-- The predictive mass is unchanged by unobserved parent and tag values. -/
theorem posteriorPred_local (h s : X.Key) (hs : s ∈ X.C h) (b b' : X.Base)
    (hv : h.2 = .interior → b.1 = b'.1)
    (hA : h.2 = .boundary → ∀ u ∈ X.binsOf (X.C h), b.2.1 u = b'.2.1 u)
    (hI : ∀ t ∈ X.C h, b.2.2 t = b'.2.2 t) :
    posteriorPred X b h s = posteriorPred X b' h s := by
  have hpost : X.hidPostDel b h s = X.hidPostDel b' h s := by
    unfold Ctx6.hidPostDel
    congr 1
    funext y
    exact hidWeight_local X h _ (Finset.erase_subset s (X.C h)) b b' hv hA
      (fun t ht => hI t (Finset.mem_of_mem_erase ht)) y
  unfold posteriorPred
  rw [hpost]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  rw [hI s hs]
  have hlaw : X.tagLawAt ((X.parOf b).set (primaryName6 h) y) s =
      X.tagLawAt ((X.parOf b').set (primaryName6 h) y) s := by
    cases hf : h.2
    · have hv' := hv hf
      simp only [Ctx6.parOf, primaryName6, hf, Par6.set]
      rw [hv']
      apply Lane_q_s06_steps1.tagLawAt_eq_of_local_interior6 X h s hs hf
      simp
    · simp only [Ctx6.parOf, primaryName6, hf, Par6.set]
      exact Lane_q_s06_steps1.tagLawAt_eq_of_local_boundary6 X h s hs y b.2.1 b'.2.1 (hA hf)
  rw [hlaw]

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
