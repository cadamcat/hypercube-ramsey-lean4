import HypercubeRamsey.S06.Steps_kernel_sol_s06_g

namespace HypercubeRamsey.S06.Lane_sol_s06_g
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)
variable {Id : Type} [Fintype Id] [DecidableEq Id]

abbrev TupleDataOn (D : Finset (Id × X.Ty)) := {e : Id × X.Ty // e ∈ D} → X.Tuple
abbrev JointObs (b : X.State) (D : Finset (Id × X.Ty)) := LocalObs X (X.tgtName b) D × TupleDataOn X D

def completeTupleData (D : Finset (Id × X.Ty)) (a : TupleDataOn X D) : X.Data Id :=
  Lane_sol_s06_steps1.fill D a (fun _ => (X.i₀, fun _ => X.y₀))

def jointReference (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty)) : FinProb (JointObs X b D) :=
  (localReference X (X.tgtName b) D).bind fun l =>
    FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.highRef (assembleLocal X v (X.tgtName b) D l) b e.1.2

def jointActual (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N) : FinProb (JointObs X b D) :=
  (localLaw X v (X.tgtName b) D ξ).bind fun l =>
    FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} =>
      X.tupleLaw (X.withParH (assembleLocal X v (X.tgtName b) D l) (X.tgtName b) ξ) e.1.2

def localPrior (v : Fin N) (b : X.State) : Law N :=
  match X.tgtName b with
  | .initial => X.initLaw
  | .candidate _ => X.candLaw v

def jointGate (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N) (ω : JointObs X b D) : Prop :=
  X.HighGate (assembleLocal X v (X.tgtName b) D ω.1) b D ξ

def jointLikelihood (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ξ : Fin N) (ω : JointObs X b D) : ℝ :=
  X.locDensity (assembleLocal X v (X.tgtName b) D ω.1) (X.tgtName b) D ξ *
    ∏ e : {e : Id × X.Ty // e ∈ D}, if drop = some e.1 then 1 else
      X.highLik (assembleLocal X v (X.tgtName b) D ω.1) b ξ e.1.2 (ω.2 e)

def jointMass (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ω : JointObs X b D) : ℝ :=
  X.s3Mass (assembleLocal X v (X.tgtName b) D ω.1) b D (completeTupleData X D ω.2) drop

 theorem completeTupleData_at (D : Finset (Id × X.Ty)) (a : TupleDataOn X D)
    (e : Id × X.Ty) (he : e ∈ D) : completeTupleData X D a e = a ⟨e, he⟩ := by
  simp [completeTupleData, Lane_sol_s06_steps1.fill, he]

 theorem assemble_prior (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty)) (l : LocalObs X (X.tgtName b) D) :
    X.priorOf (assembleLocal X v (X.tgtName b) D l) (X.tgtName b) = localPrior X v b := by
  rfl

 theorem jointMass_formula (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ω : JointObs X b D) (hm : X.stMode b = .high) :
    jointMass X v b D drop ω =
      ∑ ξ, if jointGate X v b D ξ ω then (localPrior X v b).w ξ * jointLikelihood X v b D drop ξ ω else 0 := by
  unfold jointMass Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ hξ
  simp only [Ctx6.s3Weight, hm, Ctx6.highWeight, assemble_prior]
  have hprod : (∏ e ∈ D, if drop = some e then (1 : ℝ) else
      X.highLik (assembleLocal X v (X.tgtName b) D ω.1) b ξ e.2 (completeTupleData X D ω.2 e)) =
      ∏ e : {e : Id × X.Ty // e ∈ D}, if drop = some e.1 then (1 : ℝ) else
      X.highLik (assembleLocal X v (X.tgtName b) D ω.1) b ξ e.1.2 (ω.2 e) := by
    rw [← prod_subtype D]
    apply Finset.prod_congr rfl
    intro e he
    rw [completeTupleData_at X D ω.2 e.1 e.2]
  rw [hprod]
  by_cases hg : jointGate X v b D ξ ω
  · have hg' : X.HighGate (assembleLocal X v (X.tgtName b) D ω.1) b D ξ := hg
    rw [if_pos hg, if_pos hg']
    dsimp only [jointLikelihood]
    ring
  · simp only [jointGate] at hg
    simp [hg, jointGate]

private theorem jointRatio_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ safeRatio6 a b := by
  unfold safeRatio6
  split
  · exact le_rfl
  · exact div_nonneg ha hb

 theorem local_density_nonneg (H : X.Hist) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N) :
    0 ≤ X.locDensity H nm D ξ := by
  unfold Ctx6.locDensity
  exact mul_nonneg (mul_nonneg
    (Finset.prod_nonneg fun u hu => mul_nonneg (Nat.cast_nonneg N) ((X.candLaw _).nonneg _))
    (Finset.prod_nonneg fun s hs => jointRatio_nonneg ((X.tagLawAt _ s).nonneg _) (M.Λ_nonneg _)))
    (Finset.prod_nonneg fun ℓ hℓ => mul_nonneg (Nat.cast_nonneg N) ((X.hidPost _ ℓ.1).nonneg _))

 theorem high_likelihood_nonneg (H : X.Hist) (b : X.State) (β : X.Ty) (ξ : Fin N) (o : X.Tuple) :
    0 ≤ X.highLik H b ξ β o := by
  unfold Ctx6.highLik Ctx6.tupleRatio
  exact mul_nonneg (jointRatio_nonneg ((X.Tβ _ β).nonneg _) ((tagLaw6 M).nonneg _))
    (Finset.prod_nonneg fun r hr => jointRatio_nonneg ((X.labelLaw _ _ _).nonneg _) ((X.labelLaw _ _ _).nonneg _))

 theorem jointLikelihood_nonneg (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ξ : Fin N) (ω : JointObs X b D) :
    0 ≤ jointLikelihood X v b D drop ξ ω := by
  unfold jointLikelihood
  apply mul_nonneg (local_density_nonneg X _ _ _ _)
  apply Finset.prod_nonneg
  intro e he
  split
  · norm_num
  · exact high_likelihood_nonneg X _ b e.1.2 ξ (ω.2 e)

 theorem tuple_likelihood_integral (H : X.Hist) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    (FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.highRef H b e.1.2).expect
      (fun a => ∏ e : {e : Id × X.Ty // e ∈ D}, if drop = some e.1 then 1 else X.highLik H b ξ e.1.2 (a e)) ≤ 1 := by
  let I := {e : Id × X.Ty // e ∈ D}
  let Q : I → FinProb X.Tuple := fun e => X.highRef H b e.1.2
  let f : I → X.Tuple → ℝ := fun e o => if drop = some e.1 then 1 else X.highLik H b ξ e.1.2 o
  have hf : ∀ e o, 0 ≤ f e o := by
    intro e o
    dsimp only [f]
    split
    · norm_num
    · exact high_likelihood_nonneg X H b e.1.2 ξ o
  have hi : ∀ e, ∑ o, (Q e).w o * f e o ≤ 1 := by
    intro e
    dsimp only [Q, f]
    by_cases he : drop = some e.1
    · simp [he, (X.highRef H b e.1.2).sum_eq_one]
    · simpa only [if_neg he] using high_lik_integral_le_one X H b e.1.2 ξ
  have h := Lane_q_s06_steps2.pi_product_density_le_one6 Q f hf hi
  dsimp only [Q, f] at h
  unfold FinProb.expect
  change (∑ a : I → X.Tuple, (∏ e : I, (Q e).w (a e)) * (∏ e : I, f e (a e))) ≤ 1
  convert h using 1
  congr 1
  ext a
  simp

 theorem jointLikelihood_integral (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    (jointReference X v b D).expect (jointLikelihood X v b D drop ξ) ≤ 1 := by
  unfold jointReference
  change ((localReference X (X.tgtName b) D).bind fun l =>
    FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.highRef (assembleLocal X v (X.tgtName b) D l) b e.1.2).expect
      (fun ω => jointLikelihood X v b D drop ξ (ω.1, ω.2)) ≤ 1
  rw [FinProb.bind_expect (localReference X (X.tgtName b) D)
    (fun l => FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.highRef (assembleLocal X v (X.tgtName b) D l) b e.1.2)
    (fun l a => jointLikelihood X v b D drop ξ (l, a))]
  have hinner (l : LocalObs X (X.tgtName b) D) :
      (FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.highRef (assembleLocal X v (X.tgtName b) D l) b e.1.2).expect
        (fun a => jointLikelihood X v b D drop ξ (l, a)) ≤
      X.locDensity (assembleLocal X v (X.tgtName b) D l) (X.tgtName b) D ξ := by
    let H := assembleLocal X v (X.tgtName b) D l
    have hi := tuple_likelihood_integral X H b D drop ξ
    have hn := local_density_nonneg X H (X.tgtName b) D ξ
    let Q : FinProb (TupleDataOn X D) := FinProb.pi fun e : {e : Id × X.Ty // e ∈ D} => X.highRef H b e.1.2
    let f : TupleDataOn X D → ℝ := fun a => ∏ e : {e : Id × X.Ty // e ∈ D},
      if drop = some e.1 then 1 else X.highLik H b ξ e.1.2 (a e)
    have hfactor : Q.expect (fun a => jointLikelihood X v b D drop ξ (l, a)) =
        X.locDensity H (X.tgtName b) D ξ * Q.expect f := by
      unfold FinProb.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      dsimp only [jointLikelihood, H, f]
      ring
    rw [hfactor]
    exact (mul_le_mul_of_nonneg_left hi hn).trans_eq (mul_one _)

  calc
    _ ≤ ∑ l, (localReference X (X.tgtName b) D).w l *
        X.locDensity (assembleLocal X v (X.tgtName b) D l) (X.tgtName b) D ξ :=
      Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (hinner l) ((localReference X _ D).nonneg l)
    _ ≤ ∑ l, (localLaw X v (X.tgtName b) D ξ).w l :=
      Finset.sum_le_sum fun l hl => primitive_density_le X v (X.tgtName b) D ξ l
    _ = 1 := (localLaw X v (X.tgtName b) D ξ).sum_eq_one


 theorem jointMass_nonneg (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (ω : JointObs X b D) (hm : X.stMode b = .high) :
    0 ≤ jointMass X v b D drop ω := by
  rw [jointMass_formula X v b D drop ω hm]
  apply Finset.sum_nonneg
  intro ξ hξ
  split
  · exact mul_nonneg ((localPrior X v b).nonneg ξ) (jointLikelihood_nonneg X v b D drop ξ ω)
  · exact le_rfl

 theorem jointMass_integral (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty))
    (drop : Option (Id × X.Ty)) (hm : X.stMode b = .high) :
    (jointReference X v b D).expect (jointMass X v b D drop) ≤ 1 := by
  unfold FinProb.expect
  simp_rw [jointMass_formula X v b D drop _ hm, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ ξ, (localPrior X v b).w ξ * (jointReference X v b D).expect (jointLikelihood X v b D drop ξ) := by
      apply Finset.sum_le_sum
      intro ξ hξ
      rw [FinProb.expect, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ω hω
      by_cases hg : jointGate X v b D ξ ω
      · simp only [if_pos hg]
        exact le_of_eq (by ring)
      · simp only [if_neg hg, mul_zero]
        exact mul_nonneg ((localPrior X v b).nonneg ξ)
          (mul_nonneg ((jointReference X v b D).nonneg ω) (jointLikelihood_nonneg X v b D drop ξ ω))
    _ ≤ ∑ ξ, (localPrior X v b).w ξ := by
      apply Finset.sum_le_sum
      intro ξ hξ
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (jointLikelihood_integral X v b D drop ξ) ((localPrior X v b).nonneg ξ)
    _ = 1 := (localPrior X v b).sum_eq_one

 theorem joint_mass_tests (v : Fin N) (b : X.State) (D : Finset (Id × X.Ty)) (hm : X.stMode b = .high)
    (hdom : ∀ ξ ω, jointGate X v b D ξ ω →
      (jointActual X v b D ξ).w ω ≤ (jointReference X v b D).w ω * jointLikelihood X v b D none ξ ω) :
    (∑ ξ, (localPrior X v b).w ξ * (jointActual X v b D ξ).pr
      (fun ω => jointGate X v b D ξ ω ∧ jointMass X v b D none ω < X.s3Thr) ≤ X.s3Thr) ∧
    ∀ drop : Option (Id × X.Ty),
      (∑ ξ, (localPrior X v b).w ξ * (jointActual X v b D ξ).pr
        (fun ω => jointGate X v b D ξ ω ∧ jointMass X v b D none ω < X.s3Thr * jointMass X v b D drop ω) ≤ X.s3Thr) := by
  have ht : 0 ≤ X.s3Thr := (Real.exp_pos _).le
  have hmass (ω : JointObs X b D) := jointMass_formula X v b D none ω hm
  constructor
  · exact observation_gate_mixture_bound (localPrior X v b) (jointReference X v b D)
      (jointActual X v b D) (jointGate X v b D) (jointLikelihood X v b D none)
      (jointMass X v b D none) (fun _ => X.s3Thr) X.s3Thr hmass hdom
      (Lane_q_s06_steps2.subdensity_small_mass6 (jointReference X v b D) (jointMass X v b D none) X.s3Thr ht)
  · intro drop
    exact observation_gate_mixture_bound (localPrior X v b) (jointReference X v b D)
      (jointActual X v b D) (jointGate X v b D) (jointLikelihood X v b D none)
      (jointMass X v b D none) (fun ω => X.s3Thr * jointMass X v b D drop ω) X.s3Thr hmass hdom
      (Lane_q_s06_steps2.subdensity_ratio_small_mass6 (jointReference X v b D)
        (jointMass X v b D none) (jointMass X v b D drop) X.s3Thr
        (fun ω => jointMass_nonneg X v b D drop ω hm) ht (jointMass_integral X v b D drop hm))


end
end HypercubeRamsey.S06.Lane_sol_s06_g
