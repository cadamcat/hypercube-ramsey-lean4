import HypercubeRamsey.S06.OddRows
import HypercubeRamsey.S06.OddLoads_q_s06_loads
import HypercubeRamsey.S06.Steps_bayes_sol_s06_steps1

namespace HypercubeRamsey.Lane_sol_s06_loadA

open OAI.HypercubeRamsey Classical Filter Real
open HypercubeRamsey.S06
open HypercubeRamsey.S06.Lane_sol_s06_steps1
open scoped BigOperators

noncomputable section

/-- Averaging a normalized posterior over its predictive law recovers the prior. -/
theorem posterior_mean {Y D : Type*} [Fintype Y] [Fintype D]
    (P : FinProb Y) (Q : Y → FinProb D) (y₀ y : Y) :
    (∑ d, (∑ z, P.w z * (Q z).w d) *
      (normalize6 (fun z => P.w z * (Q z).w d) y₀).w y) = P.w y := by
  have hid (d : D) : (∑ z, P.w z * (Q z).w d) *
      (normalize6 (fun z => P.w z * (Q z).w d) y₀).w y = P.w y * (Q y).w d :=
    normalize_mass_identity _ y₀ y (fun z => mul_nonneg (P.nonneg z) ((Q z).nonneg d))
  simp_rw [hid]
  rw [← Finset.mul_sum, (Q y).sum_eq_one, mul_one]

/-- True-gated expectations can be written against the deleted product law. -/
theorem gated_expect_weight_density {I Ω T : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) (F : (I → Ω) → ℝ) (z₀ : I → Ω)
    (hF : FinProb.DependsOn F S)
    (habs : ∀ i, gate i → ∀ ℓ ∈ S, ∀ y, (R ℓ).w y = 0 → (Q i ℓ).w y = 0) :
    (∑ i, P.w i * (if gate i then (FinProb.pi (Q i)).expect F else 0)) =
      (FinProb.pi R).expect (fun z => density P Q R gate S z * F z) := by
  let Q' (i : T) (ℓ : I) := if ℓ ∈ S then Q i ℓ else R ℓ
  have hchange (i : T) : (FinProb.pi (Q i)).expect F = (FinProb.pi (Q' i)).expect F :=
    pi_expect_congr_on (Q i) (Q' i) S F z₀ hF (fun ℓ hℓ => by simp [Q', hℓ])
  have hw (i : T) (hg : gate i) (z : I → Ω) :
      (FinProb.pi (Q' i)).w z = (FinProb.pi R).w z *
        ∏ ℓ ∈ S, safeRatio6 ((Q i ℓ).w (z ℓ)) ((R ℓ).w (z ℓ)) := by
    rw [← Fintype.prod_ite_mem S]
    change (∏ ℓ, (Q' i ℓ).w (z ℓ)) =
      (∏ ℓ, (R ℓ).w (z ℓ)) *
        ∏ ℓ, if ℓ ∈ S then safeRatio6 ((Q i ℓ).w (z ℓ)) ((R ℓ).w (z ℓ)) else 1
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ _
    by_cases hℓ : ℓ ∈ S
    · simp only [Q', hℓ, if_true]
      by_cases hz : (R ℓ).w (z ℓ) = 0
      · simp [hz, habs i hg ℓ hℓ (z ℓ) hz, safeRatio6]
      · simp [safeRatio6, hz, mul_div_cancel₀]
    · simp [Q', hℓ]
  have hterm (i : T) : P.w i * (if gate i then (FinProb.pi (Q i)).expect F else 0) =
      ∑ z, if gate i then P.w i * (FinProb.pi (Q' i)).w z * F z else 0 := by
    rw [hchange]
    by_cases hg : gate i <;> simp [FinProb.expect, hg, Finset.mul_sum, mul_assoc]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  unfold FinProb.expect
  apply Finset.sum_congr rfl
  intro z _
  dsimp only
  unfold density
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hg : gate i
  · simp [hg, hw i hg, mul_assoc, mul_comm, mul_left_comm]
  · simp [hg]

/-- Cancelling the posterior density bounds a gated nonnegative tag mixture by its prior mean. -/
theorem gated_posterior_mean_le {I Ω T : Type*}
    [Fintype I] [DecidableEq I] [Fintype Ω] [Fintype T]
    (P : FinProb T) (Q : T → I → FinProb Ω) (R : I → FinProb Ω)
    (gate : T → Prop) (S : Finset I) (good : (I → Ω) → Prop)
    (t₀ : T) (z₀ : I → Ω) (f : T → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hgood : ∀ z z', (∀ ℓ ∈ S, z ℓ = z' ℓ) → (good z ↔ good z'))
    (habs : ∀ i, gate i → ∀ ℓ ∈ S, ∀ y, (R ℓ).w y = 0 → (Q i ℓ).w y = 0) :
    (∑ i, P.w i * (if gate i then (FinProb.pi (Q i)).expect (fun z =>
      if good z then ∑ j, (normalize6 (fun j => P.w j * (if gate j then 1 else 0) *
        ∏ ℓ ∈ S, safeRatio6 ((Q j ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))) t₀).w j * f j else 0)
      else 0)) ≤ ∑ i, P.w i * f i := by
  let W (z : I → Ω) (j : T) := P.w j * (if gate j then 1 else 0) *
    ∏ ℓ ∈ S, safeRatio6 ((Q j ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))
  let F (z : I → Ω) := if good z then ∑ j, (normalize6 (W z) t₀).w j * f j else 0
  have hW0 (z : I → Ω) (j : T) : 0 ≤ W z j := by
    apply mul_nonneg
    · exact mul_nonneg (P.nonneg j) (by split_ifs <;> norm_num)
    · exact Finset.prod_nonneg fun ℓ _ => ratio_nonneg ((Q j ℓ).nonneg _) ((R ℓ).nonneg _)
  have hWdep (z z' : I → Ω) (hz : ∀ ℓ ∈ S, z ℓ = z' ℓ) : W z = W z' := by
    funext j
    dsimp [W]
    congr 1
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hz ℓ hℓ]
  have hF : FinProb.DependsOn F S := by
    intro z z' hz
    simp only [F, hWdep z z' hz, hgood z z' hz]
  have hpoint (z : I → Ω) : density P Q R gate S z * F z ≤ ∑ j, W z j * f j := by
    by_cases hg : good z
    · simp only [F, hg, ite_true]
      change (∑ j, W z j) * (∑ j, (normalize6 (W z) t₀).w j * f j) ≤ _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_assoc, normalize_mass_identity _ t₀ j (hW0 z)]
    · simp only [F, hg, ite_false, mul_zero]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hW0 z j) (hf j)
  change (∑ i, P.w i * (if gate i then (FinProb.pi (Q i)).expect F else 0)) ≤ _
  rw [gated_expect_weight_density P Q R gate S F z₀ hF habs]
  calc
    _ ≤ (FinProb.pi R).expect (fun z => ∑ j, W z j * f j) :=
      FinProb.expect_mono _ hpoint
    _ = ∑ j, (P.w j * (if gate j then 1 else 0) * f j) *
        (FinProb.pi R).expect (fun z =>
          ∏ ℓ ∈ S, safeRatio6 ((Q j ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))) := by
      unfold FinProb.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro z _
      dsimp [W]
      ring
    _ ≤ ∑ j, P.w j * f j := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hg : gate j
      · simp only [hg, ite_true, mul_one]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (ratio_product_integral_le_one (Q j) R S) (mul_nonneg (P.nonneg j) (hf j))
      · simp [hg, mul_nonneg (P.nonneg j) (hf j)]


/-- Posterior cancellation with an arbitrary subset of independent observations. -/
theorem product_posterior_mean {Y I D : Type*} [Fintype Y] [Fintype I]
    [DecidableEq I] [Fintype D] (P : FinProb Y) (Q : Y → I → FinProb D)
    (S : Finset I) (d₀ : D) (y₀ y : Y) :
    P.expect (fun a => (FinProb.pi (Q a)).expect (fun z =>
      (normalize6 (fun b => P.w b * ∏ i ∈ S, (Q b i).w (z i)) y₀).w y)) = P.w y := by
  let post : (I → D) → ℝ := fun z =>
    (normalize6 (fun b => P.w b * ∏ i ∈ S, (Q b i).w (z i)) y₀).w y
  have hdep : FinProb.DependsOn post S := by
    intro z z' h
    apply congrArg (fun f => (normalize6 f y₀).w y)
    funext b
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [h i hi]
  have hrestrict (a : Y) :
      (FinProb.pi (Q a)).expect post =
        (FinProb.pi (fun i : S => Q a i.1)).expect (fun z =>
          (normalize6 (fun b => P.w b * ∏ i : S, (Q b i.1).w (z i)) y₀).w y) := by
    rw [FinProb.pi_expect_depends (Q a) S post (fun _ => d₀) hdep]
    congr 1
    funext z
    dsimp [post]
    apply congrArg (fun f => (normalize6 f y₀).w y)
    funext b
    congr 1
    rw [← Finset.prod_attach S (fun i => (Q b i).w
      ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => D)).symm
        (z, fun _ => d₀) i))]
    apply Finset.prod_congr rfl
    intro i hi
    simp [Equiv.piEquivPiSubtypeProd_symm_apply, i.2]
  change P.expect (fun a => (FinProb.pi (Q a)).expect post) = _
  simp_rw [hrestrict]
  simp only [FinProb.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hBayes := posterior_mean P (fun b => FinProb.pi (fun i : S => Q b i.1)) y₀ y
  convert hBayes using 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [FinProb.pi]
  ring

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- A candidate law has the constant atom cap used in the odd base moments. -/
theorem candLaw_balanced_cap (v y : Fin N) (hv : v ∈ X.par.S₀) :
    (N : ℝ) * (X.candLaw v).w y ≤ 20 * K := by
  have hpartner := X.par.partner_cap v hv X.y₀ y
  have hmix : (N : ℝ) * (secondMixture6 M).w y ≤ K := X.hBal.2 y
  calc
    _ ≤ (N : ℝ) * (20 * (secondMixture6 M).w y) :=
      mul_le_mul_of_nonneg_left hpartner (Nat.cast_nonneg N)
    _ = 20 * ((N : ℝ) * (secondMixture6 M).w y) := by ring
    _ ≤ 20 * K := mul_le_mul_of_nonneg_left hmix (by norm_num)

/-- The primitive data at one coarse bin. -/
abbrev BinData := Fin N × (KeyFlag6 → X.ι)

/-- Independent candidates and the two tags at each bin. -/
def binLaw (v : Fin N) (w : X.Bin) : FinProb (BinData X) :=
  (X.candLaw v).bind fun a => FinProb.pi fun f : KeyFlag6 =>
    X.tagLawAt (v, Function.update (fun _ => X.y₀) w a) (w, f)

/-- Put the candidate and its two tags into one product coordinate. -/
def coarseBinEquiv : X.Coarse ≃ (X.Bin → BinData X) where
  toFun c w := (c.1 w, fun f => c.2 (w, f))
  invFun z := (fun w => (z w).1, fun k => (z k.1).2 k.2)
  left_inv c := by cases c; rfl
  right_inv z := by funext w; exact Prod.eta _

/-- The parent values at a tag's bin determine its raw tag law. -/
theorem tagLawAt_bin_local (v : Fin N) (A A' : X.Bin → Fin N) (k : X.Key)
    (hA : A k.1 = A' k.1) : X.tagLawAt (v, A) k = X.tagLawAt (v, A') k := by
  apply Lane_q_s06_steps1.tagLawAt_eq_of_parent_values6
  · cases hf : k.2 <;> simp [Par6.val, primaryName6, hf, hA]
  · cases hf : k.2 <;> simp [Par6.val, otherPrimaryName6, hf, hA]

/-- The raw coarse experiment is the product of its complete bin data. -/
theorem coarseLaw_weight (v : Fin N) (c : X.Coarse) :
    (FinProb.pi (binLaw X v)).w (coarseBinEquiv X c) = (X.coarseLaw v).w c := by
  change (∏ w, (X.candLaw v).w (c.1 w) *
    ∏ f : KeyFlag6,
      (X.tagLawAt (v, Function.update (fun _ => X.y₀) w (c.1 w)) (w, f)).w (c.2 (w, f))) =
    (∏ w, (X.candLaw v).w (c.1 w)) * ∏ k, (X.tagLawAt (v, c.1) k).w (c.2 k)
  have he (w : X.Bin) (f : KeyFlag6) :
      X.tagLawAt (v, Function.update (fun _ => X.y₀) w (c.1 w)) (w, f) =
        X.tagLawAt (v, c.1) (w, f) := tagLawAt_bin_local X v _ _ _ (by simp)
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]

/-- Expectations can be calculated using the independent per-bin law. -/
theorem coarseLaw_expect (v : Fin N) (F : X.Coarse → ℝ) :
    (X.coarseLaw v).expect F =
      (FinProb.pi (binLaw X v)).expect (fun z => F ((coarseBinEquiv X).symm z)) := by
  unfold FinProb.expect
  rw [← Equiv.sum_comp (coarseBinEquiv X)]
  apply Finset.sum_congr rfl
  intro c _
  rw [coarseLaw_weight]
  simp


set_option maxHeartbeats 400000 in
/-- The raw mean at an interior key is exactly its candidate prior. -/
theorem interior_hidPost_mean (v : Fin N) (h : X.Key) (hh : h.2 = .interior) (y : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidPost (v, c) h).w y) = (X.candLaw v).w y := by
  let A₀ : X.Bin → Fin N := fun _ => X.y₀
  let Q (a : Fin N) : X.Key → FinProb X.ι :=
    X.tagLawAt (v, Function.update A₀ h.1 a)
  let F (I : X.Key → X.ι) := (X.hidPost (v, A₀, I) h).w y
  let G (a : Fin N) := (FinProb.pi (Q a)).expect F
  have hpost (A : X.Bin → Fin N) (I : X.Key → X.ι) :
      X.hidPost (v, A, I) h = X.hidPost (v, A₀, I) h := by
    unfold Ctx6.hidPost
    congr 1
    funext z
    exact hidWeight_local X h _ (fun _ hs => hs) (v, A, I) (v, A₀, I)
      (fun _ => rfl) (by simp [hh]) (fun _ _ => rfl) z
  have hF : FinProb.DependsOn F (X.C h) := by
    intro I I' hI
    dsimp [F]
    congr 1
    unfold Ctx6.hidPost
    congr 1
    funext z
    exact hidWeight_local X h _ (fun _ hs => hs) (v, A₀, I) (v, A₀, I')
      (fun _ => rfl) (by simp [hh]) hI z
  have htags (A : X.Bin → Fin N) :
      (FinProb.pi (X.tagLawAt (v, A))).expect (fun I => (X.hidPost (v, A, I) h).w y) =
        G (A h.1) := by
    simp_rw [hpost A]
    apply pi_expect_congr_on (X.tagLawAt (v, A)) (Q (A h.1)) (X.C h) F
      (fun _ => X.i₀) hF
    intro k hk
    exact Lane_q_s06_steps1.tagLawAt_eq_of_local_interior6 X h k hk hh v A _ (by simp)
  have hdep : FinProb.DependsOn (fun A : X.Bin → Fin N => G (A h.1)) {h.1} := by
    intro A A' hA
    change G (A h.1) = G (A' h.1)
    rw [hA h.1 (Finset.mem_singleton_self _)]
  change ((FinProb.pi (fun _ : X.Bin => X.candLaw v)).bind
    (fun A => FinProb.pi (X.tagLawAt (v, A)))).expect
      (fun c => (X.hidPost (v, c) h).w y) = _
  rw [FinProb.bind_expect _ _ (fun A I => (X.hidPost (v, A, I) h).w y)]
  simp_rw [htags]
  change (FinProb.pi (fun _ : X.Bin => X.candLaw v)).expect (fun A => G (A h.1)) = _
  have hFform (I : X.Key → X.ι) :
      F I = (normalize6 (fun a => (X.candLaw v).w a *
        ∏ k ∈ X.C h, (Q a k).w (I k)) X.y₀).w y := by
    dsimp [F, Ctx6.hidPost]
    apply congrArg (fun w : Fin N → ℝ => (normalize6 w X.y₀).w y)
    funext a
    simp [Ctx6.hidWeight, Ctx6.parOf, primaryName6, hh, Par6.set, Q]
  have hMeanG : (X.candLaw v).expect G = (X.candLaw v).w y := by
    unfold G
    rw [show F = (fun I => (normalize6 (fun a => (X.candLaw v).w a *
      ∏ k ∈ X.C h, (Q a k).w (I k)) X.y₀).w y) from funext hFform]
    exact product_posterior_mean (X.candLaw v) Q (X.C h) X.i₀ X.y₀ y
  have hSingle := pi_expect_single (fun _ : X.Bin => X.candLaw v) h.1 A₀
    (fun A => G (A h.1)) hdep
  have hSample : (X.candLaw v).expect (fun a =>
      (fun A => G (A h.1)) (Function.update A₀ h.1 a)) = (X.candLaw v).expect G := by
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    exact congrArg G (Function.update_self h.1 a A₀)
  exact hSingle.trans (hSample.trans hMeanG)

/-- The Step 1 indicator can only reduce the raw interior mean. -/
theorem interior_step1_mean_le (v : Fin N) (h : X.Key) (hh : h.2 = .interior) (y : Fin N)
    (hv : v ∈ X.par.S₀) :
    (X.coarseLaw v).expect (fun c =>
      if X.Step1OK (v, c) h then (N : ℝ) * (X.hidPost (v, c) h).w y else 0) ≤ 20 * K := by
  calc
    _ ≤ (X.coarseLaw v).expect (fun c => (N : ℝ) * (X.hidPost (v, c) h).w y) := by
      apply FinProb.expect_mono
      intro c
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Nat.cast_nonneg N) ((X.hidPost (v, c) h).nonneg y)
    _ = (N : ℝ) * (X.candLaw v).w y := by
      rw [FinProb.expect_smul, interior_hidPost_mean X v h hh y]
    _ ≤ 20 * K := candLaw_balanced_cap X v y hv


/-- Step 2's tests ignore the realized base tag that is resampled in their posterior. -/
theorem step2Tests_withTag (b : X.Base) (z : X.Hid) (β : X.Ty) (i : X.ι) :
    X.Step2Tests (X.withTag b β.key i, z) β ↔ X.Step2Tests (b, z) β := by
  simp only [Ctx6.Step2Tests, tagMass_withTag]

/-- The reconstructed tag posterior ignores its actual base tag. -/
theorem Tβ_withTag (b : X.Base) (z : X.Hid) (β : X.Ty) (i : X.ι) :
    X.Tβ (X.withTag b β.key i, z) β = X.Tβ (b, z) β := by
  unfold Ctx6.Tβ Ctx6.tagPost
  congr 1
  funext j
  unfold Ctx6.tagWeight
  simp only [tagGate_withTag, hidPostRep_withTag, hidPostDel_withTag]
  rfl

/-- The true gate and the posterior normalizer cancel before averaging the base tag. -/
theorem tag_mixture_conditional_mean_le (b : X.Base) (β : X.Ty) (a : Fin N) :
    (∑ i, (X.tagLawAt (X.parOf b) β.key).w i *
      (X.hidLaw (X.withTag b β.key i)).expect (fun z =>
        (if X.tagGate (X.withTag b β.key i) β ((X.withTag b β.key i).2.2 β.key) ∧
            X.Step2Tests (X.withTag b β.key i, z) β then 1 else 0) *
          ((N : ℝ) * ∑ j, (X.Tβ (X.withTag b β.key i, z) β).w j * (M.μ j).w a))) ≤
      (N : ℝ) * ∑ i, (X.tagLawAt (X.parOf b) β.key).w i * (M.μ i).w a := by
  let P := X.tagLawAt (X.parOf b) β.key
  let Q (i : X.ι) (ℓ : X.HKey) := X.hidPostRep b ℓ.1 β.key i
  let R (ℓ : X.HKey) := X.hidPostDel b ℓ.1 β.key
  let gate := X.tagGate b β
  let good (z : X.Hid) := X.Step2Tests (b, z) β
  let f (i : X.ι) := (N : ℝ) * (M.μ i).w a
  have hf (i : X.ι) : 0 ≤ f i := mul_nonneg (Nat.cast_nonneg N) ((M.μ i).nonneg a)
  have hgood (z z' : X.Hid) (hz : ∀ ℓ ∈ β.obs, z ℓ = z' ℓ) : good z ↔ good z' :=
    Lane_q_s06_loads.step2Tests_congr_hid X b z z' β hz
  have habs : ∀ i, gate i → ∀ ℓ ∈ β.obs, ∀ y, (R ℓ).w y = 0 → (Q i ℓ).w y = 0 := by
    intro i hi ℓ hℓ y hy
    have h := hi ℓ hℓ y
    change (Q i ℓ).w y ≤ (n : ℝ) ^ d₁ * (R ℓ).w y at h
    rw [hy, mul_zero] at h
    exact le_antisymm h ((Q i ℓ).nonneg y)
  have hb := gated_posterior_mean_le P Q R gate β.obs good X.i₀ (fun _ => X.y₀) f hf hgood habs
  have hpost (z : X.Hid) :
      normalize6 (fun j => P.w j * (if gate j then 1 else 0) *
        ∏ ℓ ∈ β.obs, safeRatio6 ((Q j ℓ).w (z ℓ)) ((R ℓ).w (z ℓ))) X.i₀ =
        X.Tβ (b, z) β := rfl
  simp_rw [hpost] at hb
  have hterm (i : X.ι) :
      (X.hidLaw (X.withTag b β.key i)).expect (fun z =>
        (if X.tagGate (X.withTag b β.key i) β ((X.withTag b β.key i).2.2 β.key) ∧
            X.Step2Tests (X.withTag b β.key i, z) β then 1 else 0) *
          ((N : ℝ) * ∑ j, (X.Tβ (X.withTag b β.key i, z) β).w j * (M.μ j).w a)) =
        (if gate i then (FinProb.pi (Q i)).expect (fun z =>
          if good z then ∑ j, (X.Tβ (b, z) β).w j * f j else 0) else 0) := by
    have hv : (X.withTag b β.key i).2.2 β.key = i := by simp [Ctx6.withTag]
    simp only [hv, tagGate_withTag, step2Tests_withTag, Tβ_withTag]
    change (FinProb.pi (Q i)).expect (fun z =>
      (if gate i ∧ good z then 1 else 0) *
        ((N : ℝ) * ∑ j, (X.Tβ (b, z) β).w j * (M.μ j).w a)) = _
    by_cases hg : gate i
    · simp only [hg, true_and, ite_true]
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : good z
      · simp only [hz, ite_true, one_mul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [f]
        ring
      · simp [hz]
    · simp [hg, FinProb.expect]
  simp_rw [hterm]
  convert hb using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [f, P]
  ring


/-- The scalar whose hidden expectation is the even base summand. -/
def gatedTagMixture (H : X.Hist) (β : X.Ty) (a : Fin N) : ℝ :=
  (if X.tagGate H.1 β (H.1.2.2 β.key) ∧ X.Step2Tests H β then 1 else 0) *
    ((N : ℝ) * ∑ i, (X.Tβ H β).w i * (M.μ i).w a)

/-- A raw coarse average first cancels the base tag, leaving its original tag mixture. -/
theorem coarse_gatedTagMixture_le (v : Fin N) (β : X.Ty) (a : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v, c)).expect (fun z =>
      gatedTagMixture X ((v, c), z) β a)) ≤
      (FinProb.pi (fun _ : X.Bin => X.candLaw v)).expect (fun A =>
        (N : ℝ) * ∑ i, (X.tagLawAt (v, A) β.key).w i * (M.μ i).w a) := by
  change ((FinProb.pi (fun _ : X.Bin => X.candLaw v)).bind
    (fun A => FinProb.pi (X.tagLawAt (v, A)))).expect _ ≤ _
  rw [FinProb.bind_expect _ _ (fun A I =>
    (X.hidLaw (v, A, I)).expect (fun z => gatedTagMixture X ((v, A, I), z) β a))]
  apply FinProb.expect_mono
  intro A
  let F (I : X.Key → X.ι) := (X.hidLaw (v, A, I)).expect (fun z =>
    gatedTagMixture X ((v, A, I), z) β a)
  rw [pi_expect_resample _ β.key X.i₀ F]
  have hpoint (I : X.Key → X.ι) :
      (X.tagLawAt (v, A) β.key).expect (fun i => F (Function.update I β.key i)) ≤
        (N : ℝ) * ∑ i, (X.tagLawAt (v, A) β.key).w i * (M.μ i).w a := by
    exact tag_mixture_conditional_mean_le X (v, A, I) β a
  exact (FinProb.expect_mono _ hpoint).trans_eq (FinProb.expect_const _ _)

/-- Restricting a related parent's tag posterior costs at most `1/c₁`. -/
theorem baseTagLaw_le_eta (parent opposite : Fin N)
    (hrel : related6 E G M parent opposite) (i : X.ι) :
    (baseTagLaw6 M E G parent opposite X.i₀).w i ≤ (tagPosterior6 M parent).w i / c₁ := by
  have hmass := Lane_q_s06_steps1.baseTag_accept_mass6 (ι := X.ι) E G M parent opposite hrel.1
  have hc : 0 < c₁ := by norm_num [c₁, c₀]
  have hpos : 0 < (tagPosterior6 M parent).pr (fun j => c₁ ≤ colDeg E G (M.μ j) opposite) :=
    hc.trans_le hmass
  have hbound := Lane_q_s06_steps1.restricted_weight_le_div6 (tagPosterior6 M parent)
    (fun j => c₁ ≤ colDeg E G (M.μ j) opposite) X.i₀ i hpos
  exact hbound.trans (div_le_div_of_nonneg_left ((tagPosterior6 M parent).nonneg i) hc hmass)

/-- At an interior key, averaging its candidate prior gives a balanced tag mixture. -/
theorem interior_baseTag_mixture_mean_le (v : Fin N) (h : X.Key) (hh : h.2 = .interior)
    (hv : 0 < X.initLaw.w v) (a : Fin N) :
    (FinProb.pi (fun _ : X.Bin => X.candLaw v)).expect (fun A =>
      (N : ℝ) * ∑ i, (X.tagLawAt (v, A) h).w i * (M.μ i).w a) ≤ 20 * K / c₁ := by
  let A₀ : X.Bin → Fin N := fun _ => X.y₀
  let F (A : X.Bin → Fin N) :=
    (N : ℝ) * ∑ i, (X.tagLawAt (v, A) h).w i * (M.μ i).w a
  have hdep : FinProb.DependsOn F {h.1} := by
    intro A A' hA
    have htag := tagLawAt_bin_local X v A A' h (hA h.1 (Finset.mem_singleton_self _))
    simp only [F, htag]
  change (FinProb.pi (fun _ : X.Bin => X.candLaw v)).expect F ≤ _
  rw [pi_expect_single _ h.1 A₀ F hdep]
  have hS₀ : v ∈ X.par.S₀ := by
    have hm : 0 < X.par.piPrime.pr (fun z => z ∈ X.par.S₀) := by linarith [X.par.S₀_mass]
    exact (restrictOr6_supp hm (by simpa [Ctx6.initLaw] using hv.ne')).1
  have hc : 0 < c₁ := by norm_num [c₁, c₀]
  have hpoint (y : Fin N) : (X.candLaw v).w y * F (Function.update A₀ h.1 y) ≤
      (20 / c₁) * (N : ℝ) * (secondMixture6 M).w y *
        (∑ i, (tagPosterior6 M y).w i * (M.μ i).w a) := by
    by_cases hy : (X.candLaw v).w y = 0
    · simp only [hy, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg N))
        ((secondMixture6 M).nonneg y)) (Finset.sum_nonneg fun i _ =>
          mul_nonneg ((tagPosterior6 M y).nonneg i) ((M.μ i).nonneg a))
    have hypos : 0 < (X.candLaw v).w y :=
      lt_of_le_of_ne ((X.candLaw v).nonneg y) (Ne.symm hy)
    have hrel := (Lane_q_s06_steps1.parent_heavy_related_of_local_support X h
      (v, Function.update A₀ h.1 y, fun _ => X.i₀) hv (by simpa using hypos)).2
    have hrel' : related6 E G M y v := by
      simpa [Ctx6.parOf, Par6.val, primaryName6, otherPrimaryName6, hh] using hrel
    have ht (i : X.ι) :
        (X.tagLawAt (v, Function.update A₀ h.1 y) h).w i ≤ (tagPosterior6 M y).w i / c₁ := by
      simpa [Ctx6.tagLawAt, Par6.val, primaryName6, otherPrimaryName6, hh] using
        baseTagLaw_le_eta X y v hrel' i
    have hsum : F (Function.update A₀ h.1 y) ≤
        (N : ℝ) * (∑ i, (tagPosterior6 M y).w i * (M.μ i).w a) / c₁ := by
      dsimp [F]
      calc
        _ ≤ (N : ℝ) * ∑ i, ((tagPosterior6 M y).w i / c₁) * (M.μ i).w a :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (ht i) ((M.μ i).nonneg a)) (Nat.cast_nonneg N)
        _ = _ := by simp_rw [div_mul_eq_mul_div]; rw [← Finset.sum_div]; ring
    have hcap := X.par.partner_cap v hS₀ X.y₀ y
    calc
      _ ≤ (X.candLaw v).w y *
          ((N : ℝ) * (∑ i, (tagPosterior6 M y).w i * (M.μ i).w a) / c₁) :=
        mul_le_mul_of_nonneg_left hsum ((X.candLaw v).nonneg y)
      _ ≤ (20 * (secondMixture6 M).w y) *
          ((N : ℝ) * (∑ i, (tagPosterior6 M y).w i * (M.μ i).w a) / c₁) :=
        mul_le_mul_of_nonneg_right hcap (div_nonneg
          (mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun i _ =>
            mul_nonneg ((tagPosterior6 M y).nonneg i) ((M.μ i).nonneg a))) hc.le)
      _ = _ := by ring
  have heta : ∑ y, (secondMixture6 M).w y *
      (∑ i, (tagPosterior6 M y).w i * (M.μ i).w a) = ∑ i, M.Λ i * (M.μ i).w a := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, X.par.eta_mean i]
  calc
    _ ≤ ∑ y, (20 / c₁) * (N : ℝ) * (secondMixture6 M).w y *
        (∑ i, (tagPosterior6 M y).w i * (M.μ i).w a) := Finset.sum_le_sum fun y _ => hpoint y
    _ = (20 / c₁) * ((N : ℝ) * ∑ i, M.Λ i * (M.μ i).w a) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, heta]
    _ ≤ (20 / c₁) * K := mul_le_mul_of_nonneg_left (X.hBal.1 a) (by positivity)
    _ = 20 * K / c₁ := by ring

/-- Raw even base means at interior keys have a constant bound, before coarse avoidance. -/
theorem interior_gatedTagMixture_mean_le (v : Fin N) (β : X.Ty)
    (hh : β.key.2 = .interior) (hv : 0 < X.initLaw.w v) (a : Fin N) :
    (X.coarseLaw v).expect (fun c => (X.hidLaw (v, c)).expect (fun z =>
      gatedTagMixture X ((v, c), z) β a)) ≤ 20 * K / c₁ :=
  (coarse_gatedTagMixture_le X v β a).trans
    (interior_baseTag_mixture_mean_le X v β.key hh hv a)


/-- The true-gated even summand is nonnegative on every input. -/
theorem gatedTagMixture_nonneg (H : X.Hist) (β : X.Ty) (a : Fin N) :
    0 ≤ gatedTagMixture X H β a := by
  apply mul_nonneg
  · split_ifs <;> norm_num
  · apply mul_nonneg (Nat.cast_nonneg N)
    exact Finset.sum_nonneg fun i _ => mul_nonneg ((X.Tβ H β).nonneg i) ((M.μ i).nonneg a)

/-- On the local tests the even summand has the cap used in its moments. -/
theorem gatedTagMixture_cap (hDom : X.Step2Dom) (H : X.Hist) (β : X.Ty)
    (hβ : β ∈ X.occTypes) (hSupp : X.KeysSupp H.1 {β.key}) (a : Fin N) :
    gatedTagMixture X H β a ≤ (n : ℝ) ^ (d₂ * β.u) * K := by
  by_cases hg : X.tagGate H.1 β (H.1.2.2 β.key) ∧ X.Step2Tests H β
  · unfold gatedTagMixture
    rw [if_pos hg, one_mul]
    have htag := (hDom H β hβ hSupp hg.2).1
    calc
      _ ≤ (N : ℝ) * ∑ i, ((n : ℝ) ^ (d₂ * β.u) * M.Λ i) * (M.μ i).w a :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (htag i) ((M.μ i).nonneg a)) (Nat.cast_nonneg N)
      _ = (n : ℝ) ^ (d₂ * β.u) * ((N : ℝ) * ∑ i, M.Λ i * (M.μ i).w a) := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        ring
      _ ≤ (n : ℝ) ^ (d₂ * β.u) * K :=
        mul_le_mul_of_nonneg_left (X.hBal.1 a) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  · simp only [gatedTagMixture, hg, ite_false, zero_mul]
    have hK : 0 ≤ K := by
      exact (mul_nonneg (Nat.cast_nonneg N) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (M.Λ_nonneg i) ((M.μ i).nonneg a))).trans (X.hBal.1 a)
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hK

/-- Hidden averaging preserves the even cap. -/
theorem gatedTagMixture_hiddenMean_cap (hDom : X.Step2Dom) (b : X.Base) (β : X.Ty)
    (hβ : β ∈ X.occTypes) (hSupp : X.KeysSupp b {β.key}) (a : Fin N) :
    (X.hidLaw b).expect (fun z => gatedTagMixture X (b, z) β a) ≤ (n : ℝ) ^ (d₂ * β.u) * K :=
  (FinProb.expect_mono _ (fun z => gatedTagMixture_cap X hDom (b, z) β hβ hSupp a)).trans_eq
    (FinProb.expect_const _ _)


/-- Local functions of four independent arrays factor when their scopes are disjoint in each array. -/
theorem four_pi_expect_prod {U I₁ I₂ I₃ I₄ Ω₁ Ω₂ Ω₃ Ω₄ : Type*}
    [Fintype U] [DecidableEq U]
    [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    [Fintype I₃] [DecidableEq I₃] [Fintype I₄] [DecidableEq I₄]
    [Fintype Ω₁] [Fintype Ω₂] [Fintype Ω₃] [Fintype Ω₄]
    (P₁ : I₁ → FinProb Ω₁) (P₂ : I₂ → FinProb Ω₂)
    (P₃ : I₃ → FinProb Ω₃) (P₄ : I₄ → FinProb Ω₄)
    (s : Finset U) (S₁ : U → Finset I₁) (S₂ : U → Finset I₂)
    (S₃ : U → Finset I₃) (S₄ : U → Finset I₄)
    (F : U → (I₁ → Ω₁) → (I₂ → Ω₂) → (I₃ → Ω₃) → (I₄ → Ω₄) → ℝ)
    (h₁ : ∀ u b c d, FinProb.DependsOn (fun a => F u a b c d) (S₁ u))
    (h₂ : ∀ u a c d, FinProb.DependsOn (fun b => F u a b c d) (S₂ u))
    (h₃ : ∀ u a b d, FinProb.DependsOn (fun c => F u a b c d) (S₃ u))
    (h₄ : ∀ u a b c, FinProb.DependsOn (fun d => F u a b c d) (S₄ u))
    (hd₁ : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (S₁ u) (S₁ v))
    (hd₂ : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (S₂ u) (S₂ v))
    (hd₃ : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (S₃ u) (S₃ v))
    (hd₄ : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (S₄ u) (S₄ v)) :
    (FinProb.pi P₁).expect (fun a => (FinProb.pi P₂).expect (fun b =>
      (FinProb.pi P₃).expect (fun c => (FinProb.pi P₄).expect (fun d => ∏ u ∈ s, F u a b c d)))) =
      ∏ u ∈ s, (FinProb.pi P₁).expect (fun a => (FinProb.pi P₂).expect (fun b =>
        (FinProb.pi P₃).expect (fun c => (FinProb.pi P₄).expect (F u a b c)))) := by
  let G₃ u a b c := (FinProb.pi P₄).expect (F u a b c)
  let G₂ u a b := (FinProb.pi P₃).expect (G₃ u a b)
  let G₁ u a := (FinProb.pi P₂).expect (G₂ u a)
  have hdG₃ (u : U) (a : I₁ → Ω₁) (b : I₂ → Ω₂) :
      FinProb.DependsOn (G₃ u a b) (S₃ u) := by
    intro c c' hc
    unfold G₃ FinProb.expect
    apply Finset.sum_congr rfl
    intro d _
    exact congrArg (fun r : ℝ => (FinProb.pi P₄).w d * r) (h₃ u a b d c c' hc)
  have hdG₂ (u : U) (a : I₁ → Ω₁) : FinProb.DependsOn (G₂ u a) (S₂ u) := by
    intro b b' hb
    unfold G₂ G₃ FinProb.expect
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    exact congrArg (fun r : ℝ => (FinProb.pi P₄).w d * r) (h₂ u a c d b b' hb)
  have hdG₁ (u : U) : FinProb.DependsOn (G₁ u) (S₁ u) := by
    intro a a' ha
    unfold G₁ G₂ G₃ FinProb.expect
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    exact congrArg (fun r : ℝ => (FinProb.pi P₄).w d * r) (h₁ u b c d a a' ha)
  have he₄ (a : I₁ → Ω₁) (b : I₂ → Ω₂) (c : I₃ → Ω₃) :
      (FinProb.pi P₄).expect (fun d => ∏ u ∈ s, F u a b c d) = ∏ u ∈ s, G₃ u a b c :=
    Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint P₄ s S₄
      (fun u d => F u a b c d) (fun u => h₄ u a b c) hd₄
  have he₃ (a : I₁ → Ω₁) (b : I₂ → Ω₂) :
      (FinProb.pi P₃).expect (fun c => ∏ u ∈ s, G₃ u a b c) = ∏ u ∈ s, G₂ u a b :=
    Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint P₃ s S₃ (fun u => G₃ u a b) (fun u => hdG₃ u a b) hd₃
  have he₂ (a : I₁ → Ω₁) :
      (FinProb.pi P₂).expect (fun b => ∏ u ∈ s, G₂ u a b) = ∏ u ∈ s, G₁ u a :=
    Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint P₂ s S₂ (fun u => G₂ u a) (fun u => hdG₂ u a) hd₂
  simp_rw [he₄, he₃, he₂]
  exact Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint P₁ s S₁ G₁ hdG₁ hd₁


/-- Rows are nonnegative, including the zero row on invalid inputs. -/
theorem oddRow_nonneg (H : X.Hist) (C : X.Centre) (u : CubeVertex n) (y : Fin N) :
    0 ≤ X.oddRow H C u y := by
  unfold Ctx6.oddRow Ctx6.oddRowAt
  split_ifs
  · cases X.stMode (X.g.L.stateOf u) with
    | low => exact (X.lowRow H (X.pos C) (X.g.L.stateOf u)
        (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)).nonneg y
    | high => exact (X.s3Post H (X.g.L.stateOf u)
        (X.actDesc H C X.Rlong (X.g.L.stateOf u)) (X.tup C)).nonneg y
  · exact le_rfl

/-- The centre moment cap applies on every centre outcome; invalid rows vanish. -/
theorem oddRow_cap (hRows : X.OddRowBounds) (H : X.Hist) (hH : X.histLaw.w H ≠ 0)
    (C : X.Centre) (u : CubeVertex n) (hu : ¬ IsEvenRole u) (y : Fin N) :
    (N : ℝ) * X.oddRow H C u y ≤
      max (Real.exp ((X.m : ℝ) ^ (15 / 100 : ℝ))) ((n : ℝ) ^ ((5 / 100 : ℝ) * X.J)) := by
  by_cases hv : X.OddValid H C X.Rlong (X.g.L.stateOf u)
  · have hcap := (hRows H C u hH hu hv).2.2.1 y
    exact hcap.trans (by split_ifs <;> [exact le_max_left _ _; exact le_max_right _ _])
  · simp only [Ctx6.oddRow, Ctx6.oddRowAt, hv, ite_false, mul_zero]
    exact (Real.exp_pos _).le.trans (le_max_left _ _)

/-- The four-array factorization specializes to the raw centre experiment. -/
theorem centreLaw_expect_prod_of_scopes {U : Type*} [Fintype U] [DecidableEq U]
    (H : X.Hist) (s : Finset U) (SP : U → Finset X.Loc)
    (SO : U → Finset (X.Loc × X.Ty)) (SA ST : U → Finset X.Loc)
    (f : U → X.Centre → ℝ)
    (hP : ∀ u O A τ, FinProb.DependsOn (fun P => f u (((P, O), A), τ)) (SP u))
    (hO : ∀ u P A τ, FinProb.DependsOn (fun O => f u (((P, O), A), τ)) (SO u))
    (hA : ∀ u P O τ, FinProb.DependsOn (fun A => f u (((P, O), A), τ)) (SA u))
    (hT : ∀ u P O A, FinProb.DependsOn (fun τ => f u (((P, O), A), τ)) (ST u))
    (hdP : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (SP u) (SP v))
    (hdO : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (SO u) (SO v))
    (hdA : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (SA u) (SA v))
    (hdT : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Disjoint (ST u) (ST v)) :
    (X.centreLaw H).expect (fun C => ∏ u ∈ s, f u C) =
      ∏ u ∈ s, (X.centreLaw H).expect (f u) := by
  have hrepr (g : X.Centre → ℝ) :
      (X.centreLaw H).expect g = X.hp.posLaw.expect (fun P => (X.dataLaw X.Loc H).expect
        (fun O => X.hp.actLaw.expect (fun A => X.hp.tieLaw.expect (fun τ => g (((P, O), A), τ))))) := by
    unfold Ctx6.centreLaw
    rw [Lane_q_s06_loads.finProb_prod_expect, Lane_q_s06_loads.finProb_prod_expect,
      Lane_q_s06_loads.finProb_prod_expect]
  simp_rw [hrepr]
  exact four_pi_expect_prod
    (fun _ => FinProb.bernoulli (X.hp.lam / (X.hp.V : ℝ)))
    (fun e : X.Loc × X.Ty => X.tupleLaw H e.2)
    (fun _ => FinProb.bernoulli ((X.hp.n : ℝ) ^ X.hp.b₀ / X.hp.lam))
    (fun _ => (FinProb.uniformAll ⟨1⟩ : FinProb X.hp.TiePerm))
    s SP SO SA ST (fun u P O A τ => f u (((P, O), A), τ)) hP hO hA hT hdP hdO hdA hdT


/-- Every state visited by a height computation is in its consultation ball. -/
theorem reach_in_consultation_ball (p : HDParams) (Sites : p.Sites)
    (P A : p.Loc → Bool) (Esel : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    {v : CubeVertex p.d} {j : ℕ} (h : p.Reach Sites P A Esel q R v j) :
    v ∈ Sites ∧ _root_.hammingDist v q ≤ R := by
  induction h with
  | start v hv hR => exact ⟨hv, hR⟩
  | up _ _ _ _ _ ih => exact ih
  | down _ _ _ _ hv hR _ _ => exact ⟨hv, hR⟩

/-- A height path reads only bad-level indicators in its consultation ball. -/
theorem reach_mono_of_bad (p : HDParams) (Sites : p.Sites)
    (P A P' A' : p.Loc → Bool) (Esel Esel' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ v ∈ Sites, _root_.hammingDist v q ≤ R → ∀ j,
      p.BadN P A Esel v j → p.BadN P' A' Esel' v j)
    {v : CubeVertex p.d} {j : ℕ} (h : p.Reach Sites P A Esel q R v j) :
    p.Reach Sites P' A' Esel' q R v j := by
  induction h with
  | start v hv hR => exact .start v hv hR
  | up v j hj hreach hb ih =>
      have hloc := reach_in_consultation_ball p Sites P A Esel q R hreach
      exact .up v j hj ih (hbad v hloc.1 hloc.2 j hb)
  | down v v' j _ hv hR hD ih => exact .down v v' j ih hv hR hD

/-- Equal local bad-level indicators produce the same height computation. -/
theorem height_congr_of_bad (p : HDParams) (Sites : p.Sites)
    (P A P' A' : p.Loc → Bool) (Esel Esel' : p.EligMap) (q : CubeVertex p.d) (R : ℕ)
    (hbad : ∀ v ∈ Sites, _root_.hammingDist v q ≤ R → ∀ j,
      p.BadN P A Esel v j ↔ p.BadN P' A' Esel' v j) :
    p.height Sites P A Esel R q = p.height Sites P' A' Esel' R q := by
  have hreach (v : CubeVertex p.d) (j : ℕ) :
      p.Reach Sites P A Esel q R v j ↔ p.Reach Sites P' A' Esel' q R v j := by
    constructor
    · exact reach_mono_of_bad p Sites P A P' A' Esel Esel' q R
        (fun v hv hR j => (hbad v hv hR j).mp)
    · exact reach_mono_of_bad p Sites P' A' P A Esel' Esel q R
        (fun v hv hR j => (hbad v hv hR j).mpr)
  unfold HDParams.height
  congr 1
  ext j
  simp only [Finset.mem_filter, hreach]


/-- The odd base summand, before restricting to odd roles. -/
def baseLoadTerm (b : X.Base) (u : CubeVertex n) (y : Fin N) : ℝ :=
  if X.stMode (X.g.L.stateOf u) = .low ∧ X.Step1OK b (X.tgt (X.g.L.stateOf u)).1 then
    (N : ℝ) * (X.hidPost b (X.tgt (X.g.L.stateOf u)).1).w y else 0

theorem baseLoadTerm_nonneg (b : X.Base) (u : CubeVertex n) (y : Fin N) :
    0 ≤ baseLoadTerm X b u y := by
  unfold baseLoadTerm
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg N) ((X.hidPost b _).nonneg y)
  · exact le_rfl

theorem baseLoadTerm_cap (b : X.Base) (u : CubeVertex n) (y : Fin N) :
    baseLoadTerm X b u y ≤ (n : ℝ) ^ d₁ := by
  unfold baseLoadTerm
  split_ifs with h
  · exact h.2.1 y
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- The boundary contribution is negligible even before any conditioning. -/
theorem boundary_baseLoadTerm_average_le (b : X.Base) (y : Fin N) (hn : 0 < n) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ u : CubeVertex n,
      (if X.g.L.boundary u then baseLoadTerm X b u y else 0) ≤
        (n : ℝ) ^ (-(1 / 20 : ℝ) + d₁) := by
  let B : Finset (CubeVertex n) := Finset.univ.filter X.g.L.boundary
  have hsum : (∑ u : CubeVertex n, if X.g.L.boundary u then baseLoadTerm X b u y else 0) ≤
      (B.card : ℝ) * (n : ℝ) ^ d₁ := by
    rw [← Finset.sum_filter]
    calc
      _ ≤ ∑ u ∈ B, (n : ℝ) ^ d₁ := Finset.sum_le_sum fun u _ => baseLoadTerm_cap X b u y
      _ = _ := by simp
  have hboundary : (B.card : ℝ) / (2 : ℝ) ^ n ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) :=
    X.g.boundary_fraction
  calc
    _ ≤ ((2 : ℝ) ^ n)⁻¹ * ((B.card : ℝ) * (n : ℝ) ^ d₁) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((B.card : ℝ) / (2 : ℝ) ^ n) * (n : ℝ) ^ d₁ := by ring
    _ ≤ (n : ℝ) ^ (-(1 / 20 : ℝ)) * (n : ℝ) ^ d₁ :=
      mul_le_mul_of_nonneg_right hboundary (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = _ := (Real.rpow_add (by exact_mod_cast hn) _ _).symm

/-- The boundary bound tends to zero with the fixed Step 1 exponent. -/
theorem boundary_baseLoadTerm_eventually_small :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-(1 / 20 : ℝ) + d₁) ≤ 1 := by
  have he : 0 < (1 / 20 : ℝ) - d₁ := by norm_num [d₁]
  have ht := (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop
  have hn : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ (-((1 / 20 : ℝ) - d₁)) < 1 :=
    ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hn] with n hn
  have heq : -((1 / 20 : ℝ) - d₁) = -(1 / 20 : ℝ) + d₁ := by ring
  rw [heq] at hn
  exact hn.le


/-- Height selection reads activations only on its eligible IDs and ties only at the queried site. -/
theorem selectionAt_congr (p : HDParams) (Sites : p.Sites)
    (P A P' A' : p.Loc → Bool) (Esel Esel' : p.EligMap) (τ τ' : p.Ties)
    (q : CubeVertex p.d) (R : ℕ)
    (hheight : p.height Sites P A Esel R q = p.height Sites P' A' Esel' R q)
    (hbad : ∀ j, p.Bad P A Esel q j ↔ p.Bad P' A' Esel' q j)
    (hE : ∀ j, Esel q j = Esel' q j)
    (hA : ∀ j ℓ, ℓ ∈ Esel q j → A ℓ = A' ℓ)
    (hτ : ∀ j, τ (q, j) = τ' (q, j)) :
    p.selectionAt Sites P A Esel τ R q = p.selectionAt Sites P' A' Esel' τ' R q := by
  have hfilter (j : Fin (p.H + 1)) :
      (Esel' q j).filter (fun ℓ => A ℓ = true) = (Esel' q j).filter (fun ℓ => A' ℓ = true) := by
    apply Finset.filter_congr
    intro ℓ hℓ
    have hmem : ℓ ∈ Esel q j := by rw [hE j]; exact hℓ
    rw [hA j ℓ hmem]
  unfold HDParams.selectionAt
  simp only [hheight, hbad, hE, HDParams.priority, hτ, hfilter]
  rfl


/-- Interior posteriors and Step 1 tests read only the tags in their own bin. -/
theorem interior_step1_depends_on_bin (v : Fin N) (h : X.Key) (hh : h.2 = .interior) (y : Fin N) :
    FinProb.DependsOn (fun z : X.Bin → BinData X =>
      if X.Step1OK (v, (coarseBinEquiv X).symm z) h then
        (N : ℝ) * (X.hidPost (v, (coarseBinEquiv X).symm z) h).w y else 0) {h.1} := by
  intro z z' hz
  let b : X.Base := (v, (coarseBinEquiv X).symm z)
  let b' : X.Base := (v, (coarseBinEquiv X).symm z')
  have htags : ∀ k ∈ X.C h, b.2.2 k = b'.2.2 k := by
    intro k hk
    have hbin := Lane_q_s06_steps1.keyNeighbor_bin_eq_of_interior6 binAdjacent6 h k
      (by simpa [Ctx6.C] using hk) hh
    change (z k.1).2 k.2 = (z' k.1).2 k.2
    rw [hbin, hz h.1 (Finset.mem_singleton_self _)]
  have hweights (S : Finset X.Key) (hS : S ⊆ X.C h) :
      X.hidWeight b h S = X.hidWeight b' h S := by
    funext a
    exact hidWeight_local X h S hS b b' (fun _ => rfl) (by simp [hh])
      (fun k hk => htags k (hS hk)) a
  have hpost : X.hidPost b h = X.hidPost b' h := by
    unfold Ctx6.hidPost
    rw [hweights _ (fun _ hk => hk)]
  have hdel (k : X.Key) : X.hidPostDel b h k = X.hidPostDel b' h k := by
    unfold Ctx6.hidPostDel
    rw [hweights _ (Finset.erase_subset _ _)]
  have hok : X.Step1OK b h ↔ X.Step1OK b' h := by
    simp only [Ctx6.Step1OK, Ctx6.Step1Cap, Ctx6.Step1Del, hpost, hdel]
  change (if X.Step1OK b h then (N : ℝ) * (X.hidPost b h).w y else 0) =
    (if X.Step1OK b' h then (N : ℝ) * (X.hidPost b' h).w y else 0)
  simp only [hok, hpost]

/-- Distinct interior bins have raw product means bounded by the product of candidate caps. -/
theorem interior_step1_product_raw_le {U : Type*} [Fintype U] [DecidableEq U]
    (v : Fin N) (hv : v ∈ X.par.S₀) (s : Finset U) (h : U → X.Key)
    (hh : ∀ u, (h u).2 = .interior)
    (hsep : ∀ u ∈ s, ∀ u' ∈ s, u ≠ u' → (h u).1 ≠ (h u').1) (y : Fin N) :
    (X.coarseLaw v).expect (fun c => ∏ u ∈ s,
      (if X.Step1OK (v, c) (h u) then (N : ℝ) * (X.hidPost (v, c) (h u)).w y else 0)) ≤
        (20 * K) ^ s.card := by
  let F (u : U) (z : X.Bin → BinData X) :=
    if X.Step1OK (v, (coarseBinEquiv X).symm z) (h u) then
      (N : ℝ) * (X.hidPost (v, (coarseBinEquiv X).symm z) (h u)).w y else 0
  have hdep (u : U) : FinProb.DependsOn (F u) {(h u).1} :=
    interior_step1_depends_on_bin X v (h u) (hh u) y
  have hdis : ∀ u ∈ s, ∀ u' ∈ s, u ≠ u' → Disjoint ({(h u).1} : Finset X.Bin) {(h u').1} := by
    intro u hu u' hu' hne
    simpa using hsep u hu u' hu' hne
  have hfactor := Lane_q_s06_loads.pi_expect_prod_pairwise_disjoint
    (binLaw X v) s (fun u => {(h u).1}) F hdep hdis
  have hmean (u : U) : (FinProb.pi (binLaw X v)).expect (F u) ≤ 20 * K := by
    rw [← coarseLaw_expect X v (fun c =>
      if X.Step1OK (v, c) (h u) then (N : ℝ) * (X.hidPost (v, c) (h u)).w y else 0)]
    exact interior_step1_mean_le X v (h u) (hh u) y hv
  have hnonneg (u : U) : 0 ≤ (FinProb.pi (binLaw X v)).expect (F u) := by
    apply Finset.sum_nonneg
    intro z _
    apply mul_nonneg ((FinProb.pi (binLaw X v)).nonneg z)
    dsimp [F]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg N) ((X.hidPost _ _).nonneg y)
    · exact le_rfl
  rw [coarseLaw_expect X v]
  change (FinProb.pi (binLaw X v)).expect (fun z => ∏ u ∈ s, F u z) ≤ _
  rw [hfactor]
  calc
    _ ≤ ∏ _u ∈ s, 20 * K := Finset.prod_le_prod₀ (fun u _ => hnonneg u) (fun u _ => hmean u)
    _ = _ := by simp

/-- Agreement of the parent and the complete data at the listed bins. -/
structure BaseAgree (S : Finset X.Bin) (b b' : X.Base) : Prop where
  initial : b.1 = b'.1
  candidate : ∀ w ∈ S, b.2.1 w = b'.2.1 w
  tag : ∀ k : X.Key, k.1 ∈ S → b.2.2 k = b'.2.2 k

theorem BaseAgree.mono {S T : Finset X.Bin} {b b' : X.Base}
    (h : BaseAgree X T b b') (hST : S ⊆ T) : BaseAgree X S b b' :=
  ⟨h.initial, fun w hw => h.candidate w (hST hw), fun k hk => h.tag k (hST hk)⟩

theorem BaseAgree.withTag {S : Finset X.Bin} {b b' : X.Base}
    (h : BaseAgree X S b b') (k : X.Key) (i : X.ι) :
    BaseAgree X S (X.withTag b k i) (X.withTag b' k i) := by
  refine ⟨h.initial, h.candidate, ?_⟩
  intro s hs
  by_cases hsk : s = k
  · subst s; simp [Ctx6.withTag]
  · simp [Ctx6.withTag, Function.update_of_ne hsk, h.tag s hs]

theorem BaseAgree.withPar {S : Finset X.Bin} {b b' : X.Base}
    (h : BaseAgree X S b b') (nm : ParentName6 X.Bin) (ξ : Fin N) :
    BaseAgree X S (X.withPar b nm ξ) (X.withPar b' nm ξ) := by
  cases nm with
  | initial => exact ⟨rfl, h.candidate, h.tag⟩
  | candidate w =>
    refine ⟨h.initial, ?_, h.tag⟩
    intro u hu
    by_cases huw : u = w
    · subst u; simp [Ctx6.withPar, Ctx6.parOf, Par6.set]
    · simp [Ctx6.withPar, Ctx6.parOf, Par6.set, Function.update_of_ne huw,
        h.candidate u hu]

theorem bin_mem_posteriorScope (h : X.Key) : h.1 ∈ X.binsOf (X.C h) := by
  apply Finset.mem_image.mpr
  exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩, rfl⟩

theorem hidWeight_congr_base (h : X.Key) (S : Finset X.Key) (hS : S ⊆ X.C h)
    (b b' : X.Base) (hb : BaseAgree X (X.binsOf (X.C h)) b b') :
    X.hidWeight b h S = X.hidWeight b' h S := by
  funext y
  apply hidWeight_local X h S hS b b' (fun _ => hb.initial) (fun _ => hb.candidate)
  intro k hk
  exact hb.tag k (Finset.mem_image.mpr ⟨k, hS hk, rfl⟩)

theorem hidPost_congr_base (h : X.Key) (b b' : X.Base)
    (hb : BaseAgree X (X.binsOf (X.C h)) b b') : X.hidPost b h = X.hidPost b' h := by
  unfold Ctx6.hidPost
  rw [hidWeight_congr_base X h _ Finset.Subset.rfl b b' hb]

theorem hidPostDel_congr_base (h k : X.Key) (b b' : X.Base)
    (hb : BaseAgree X (X.binsOf (X.C h)) b b') :
    X.hidPostDel b h k = X.hidPostDel b' h k := by
  unfold Ctx6.hidPostDel
  rw [hidWeight_congr_base X h _ (Finset.erase_subset _ _) b b' hb]

theorem hidPostRep_congr_base (h k : X.Key) (i : X.ι) (b b' : X.Base)
    (hb : BaseAgree X (X.binsOf (X.C h)) b b') :
    X.hidPostRep b h k i = X.hidPostRep b' h k i :=
  hidPost_congr_base X h _ _ (hb.withTag X k i)

theorem step1OK_congr_base (h : X.Key) (b b' : X.Base)
    (hb : BaseAgree X (X.binsOf (X.C h)) b b') : X.Step1OK b h ↔ X.Step1OK b' h := by
  simp only [Ctx6.Step1OK, Ctx6.Step1Cap, Ctx6.Step1Del,
    hidPost_congr_base X h b b' hb, hidPostDel_congr_base X h _ b b' hb]

/-- The complete coarse inputs of one type, including its realized base tag. -/
def typeBaseScope (β : X.Ty) : Finset X.Bin :=
  insert β.key.1 (β.obs.biUnion fun ℓ => X.binsOf (X.C ℓ.1))

theorem typeBaseScope_obs (β : X.Ty) (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
    X.binsOf (X.C ℓ.1) ⊆ typeBaseScope X β := by
  intro w hw
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hw⟩)

theorem tagGate_congr_base (β : X.Ty) (i : X.ι) (b b' : X.Base)
    (hb : BaseAgree X (typeBaseScope X β) b b') : X.tagGate b β i ↔ X.tagGate b' β i := by
  unfold Ctx6.tagGate
  apply forall₂_congr
  intro ℓ hℓ
  have hlocal := hb.mono X (typeBaseScope_obs X β ℓ hℓ)
  rw [hidPostRep_congr_base X ℓ.1 β.key i b b' hlocal,
    hidPostDel_congr_base X ℓ.1 β.key b b' hlocal]

theorem tagWeight_congr_base (β : X.Ty) (S : Finset X.HKey) (hS : S ⊆ β.obs)
    (i : X.ι) (b b' : X.Base) (Z : X.Hid)
    (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.tagWeight (b, Z) β S i = X.tagWeight (b', Z) β S i := by
  have hkey : β.key.1 ∈ typeBaseScope X β := Finset.mem_insert_self _ _
  have hlaw : X.tagLawAt (X.parOf b) β.key = X.tagLawAt (X.parOf b') β.key := by
    change X.tagLawAt (b.1, b.2.1) β.key = X.tagLawAt (b'.1, b'.2.1) β.key
    rw [hb.initial]
    exact tagLawAt_bin_local X b'.1 _ _ β.key (hb.candidate _ hkey)
  unfold Ctx6.tagWeight
  rw [hlaw, tagGate_congr_base X β i b b' hb]
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  have hlocal := hb.mono X (typeBaseScope_obs X β ℓ (hS hℓ))
  rw [hidPostRep_congr_base X ℓ.1 β.key i b b' hlocal,
    hidPostDel_congr_base X ℓ.1 β.key b b' hlocal]

theorem tagMass_congr_base (β : X.Ty) (S : Finset X.HKey) (hS : S ⊆ β.obs)
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.tagMass (b, Z) β S = X.tagMass (b', Z) β S := by
  unfold Ctx6.tagMass
  exact Finset.sum_congr rfl (fun i _ => tagWeight_congr_base X β S hS i b b' Z hb)

theorem tagPost_congr_base (β : X.Ty) (S : Finset X.HKey) (hS : S ⊆ β.obs)
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.tagPost (b, Z) β S = X.tagPost (b', Z) β S := by
  have hw : X.tagWeight (b, Z) β S = X.tagWeight (b', Z) β S :=
    funext (fun i => tagWeight_congr_base X β S hS i b b' Z hb)
  unfold Ctx6.tagPost
  rw [hw]

theorem step2Tests_congr_base (β : X.Ty) (b b' : X.Base) (Z : X.Hid)
    (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.Step2Tests (b, Z) β ↔ X.Step2Tests (b', Z) β := by
  simp only [Ctx6.Step2Tests, tagMass_congr_base X β β.obs Finset.Subset.rfl b b' Z hb,
    tagMass_congr_base X β _ (Finset.erase_subset _ _) b b' Z hb]

theorem step2Fail_congr_base (β : X.Ty) (b b' : X.Base) (Z : X.Hid)
    (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.Step2Fail (b, Z) β ↔ X.Step2Fail (b', Z) β := by
  have hi := hb.tag β.key (Finset.mem_insert_self _ _)
  simp only [Ctx6.Step2Fail, hi, tagGate_congr_base X β _ b b' hb,
    step2Tests_congr_base X β b b' Z hb]

theorem rate2Base_congr_base (β : X.Ty) (b b' : X.Base)
    (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.rate2Base b β = X.rate2Base b' β := by
  have hdep : FinProb.DependsOn (fun Z : X.Hid => X.Step2Fail (b', Z) β) β.obs := by
    intro Z Z' hZ
    exact propext (Lane_q_s06_stages.step2Fail_iff_of_agree X b' β Z Z' hZ)
  have hlaws (ℓ : X.HKey) (hℓ : ℓ ∈ β.obs) :
      X.hidPost b ℓ.1 = X.hidPost b' ℓ.1 :=
    hidPost_congr_base X ℓ.1 b b' (hb.mono X (typeBaseScope_obs X β ℓ hℓ))
  unfold Ctx6.rate2Base
  have hevent : (fun Z : X.Hid => X.Step2Fail (b, Z) β) =
      (fun Z : X.Hid => X.Step2Fail (b', Z) β) :=
    funext (fun Z => propext (step2Fail_congr_base X β b b' Z hb))
  rw [hevent]
  exact Lane_q_s06_stages.pi_pr_eq_of_kernel_eq_on_depends _ _ β.obs _ hdep hlaws

theorem reqNames_congr_base (β : X.Ty) (b b' : X.Base) (Z : X.Hid)
    (hb : BaseAgree X (typeBaseScope X β) b b') :
    ∀ nm ∈ reqNames6 β, X.varVal (b, Z) nm = X.varVal (b', Z) nm := by
  intro nm hnm
  have hprimary : (X.parOf b).val (primaryName6 β.key) =
      (X.parOf b').val (primaryName6 β.key) := by
    cases hf : β.key.2 <;> simp [Ctx6.parOf, primaryName6, Par6.val, hf,
      hb.initial, hb.candidate β.key.1 (Finset.mem_insert_self _ _)]
  have hother : (X.parOf b).val (otherPrimaryName6 β.key) =
      (X.parOf b').val (otherPrimaryName6 β.key) := by
    cases hf : β.key.2 <;> simp [Ctx6.parOf, otherPrimaryName6, Par6.val, hf,
      hb.initial, hb.candidate β.key.1 (Finset.mem_insert_self _ _)]
  cases nm with
  | hid ℓ => rfl
  | par p =>
    have hp : p = primaryName6 β.key ∨ p = otherPrimaryName6 β.key := by
      by_cases hm : β.mode = .high
      · simpa [reqNames6, hm] using hnm
      · have hp : p = primaryName6 β.key := by simpa [reqNames6, hm] using hnm
        exact Or.inl hp
    rcases hp with rfl | rfl
    · exact hprimary
    · exact hother

theorem tupleLaw_congr_base (β : X.Ty) (b b' : X.Base) (Z : X.Hid)
    (hb : BaseAgree X (typeBaseScope X β) b b') :
    X.tupleLaw (b, Z) β = X.tupleLaw (b', Z) β := by
  unfold Ctx6.tupleLaw Ctx6.Tβ
  rw [tagPost_congr_base X β β.obs Finset.Subset.rfl b b' Z hb]
  exact _root_.Lane_q_s06_loads.tupleLawOn_congr_varVal X _ _ _ _
    (reqNames_congr_base X β b b' Z hb)

variable {Id : Type} [Fintype Id] [DecidableEq Id]

/-- Coarse observations for a descriptor, including its low target prior. -/
def descBaseScope (b : X.State) (D : Finset (Id × X.Ty)) : Finset X.Bin :=
  X.binsOf (X.C (X.tgt b).1) ∪ D.biUnion (fun e => typeBaseScope X e.2)

theorem descBaseScope_type (b : X.State) (D : Finset (Id × X.Ty))
    (e : Id × X.Ty) (he : e ∈ D) : typeBaseScope X e.2 ⊆ descBaseScope X b D := by
  intro w hw
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, he, hw⟩)

theorem descBaseScope_obs (b : X.State) (D : Finset (Id × X.Ty))
    (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D) : X.binsOf (X.C ℓ.1) ⊆ descBaseScope X b D := by
  obtain ⟨e, he, hobs⟩ := Finset.mem_biUnion.mp hℓ
  exact (typeBaseScope_obs X e.2 ℓ hobs).trans (descBaseScope_type X b D e he)

theorem descBaseScope_key (b : X.State) (D : Finset (Id × X.Ty))
    (k : X.Key) (hk : k ∈ X.locKeys D) : k.1 ∈ descBaseScope X b D := by
  rcases Finset.mem_union.mp hk with hk | hk
  · obtain ⟨ℓ, hℓ, hk⟩ := Finset.mem_biUnion.mp hk
    exact descBaseScope_obs X b D ℓ hℓ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hk
    exact descBaseScope_type X b D e he (Finset.mem_insert_self _ _)

theorem lowGate_congr_base (s : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.LowGate (b, Z) s D ξ ↔ X.LowGate (b', Z) s D ξ := by
  have ht := hb.mono X (Finset.subset_union_left)
  have htests : ∀ e ∈ D, X.Step2Tests (X.withHid (b, Z) (X.tgt s) ξ) e.2 =
      X.Step2Tests (X.withHid (b', Z) (X.tgt s) ξ) e.2 := by
    intro e he
    exact propext (step2Tests_congr_base X e.2 b b' _
      (hb.mono X (descBaseScope_type X s D e he)))
  have hforall : (∀ e ∈ D, X.Step2Tests (X.withHid (b, Z) (X.tgt s) ξ) e.2) ↔
      ∀ e ∈ D, X.Step2Tests (X.withHid (b', Z) (X.tgt s) ξ) e.2 := by
    apply forall₂_congr
    intro e he
    exact Iff.of_eq (htests e he)
  simp only [Ctx6.LowGate, Ctx6.Step1Cap, hidPost_congr_base X _ b b' ht, hforall]

theorem highGate_congr_base (s : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.HighGate (b, Z) s D ξ ↔ X.HighGate (b', Z) s D ξ := by
  have hprior : X.priorOf (b, Z) (X.tgtName s) = X.priorOf (b', Z) (X.tgtName s) := by
    cases X.tgtName s <;> simp [Ctx6.priorOf, hb.initial]
  have hp := hb.withPar X (X.tgtName s) ξ
  have htests : ∀ e ∈ D, X.Step2Tests (X.withParH (b, Z) (X.tgtName s) ξ) e.2 =
      X.Step2Tests (X.withParH (b', Z) (X.tgtName s) ξ) e.2 := by
    intro e he
    exact propext (step2Tests_congr_base X e.2 _ _ _
      (hp.mono X (descBaseScope_type X s D e he)))
  have hsteps : ∀ ℓ ∈ X.locHid D,
      X.Step1OK (X.withParH (b, Z) (X.tgtName s) ξ).1 ℓ.1 =
      X.Step1OK (X.withParH (b', Z) (X.tgtName s) ξ).1 ℓ.1 := by
    intro ℓ hℓ
    exact propext (step1OK_congr_base X ℓ.1 _ _
      (hp.mono X (descBaseScope_obs X s D ℓ hℓ)))
  have hforallSteps : (∀ ℓ ∈ X.locHid D,
      X.Step1OK (X.withParH (b, Z) (X.tgtName s) ξ).1 ℓ.1) ↔
      ∀ ℓ ∈ X.locHid D, X.Step1OK (X.withParH (b', Z) (X.tgtName s) ξ).1 ℓ.1 := by
    apply forall₂_congr
    intro ℓ hℓ
    exact Iff.of_eq (hsteps ℓ hℓ)
  have hforallTests : (∀ e ∈ D, X.Step2Tests (X.withParH (b, Z) (X.tgtName s) ξ) e.2) ↔
      ∀ e ∈ D, X.Step2Tests (X.withParH (b', Z) (X.tgtName s) ξ) e.2 := by
    apply forall₂_congr
    intro e he
    exact Iff.of_eq (htests e he)
  simp only [Ctx6.HighGate, hprior, hforallSteps, hforallTests]

theorem tupleRatio_congr_base (β : X.Ty) (b b' c c' : X.Base) (Z W : X.Hid)
    (hb : BaseAgree X (typeBaseScope X β) b b')
    (hc : BaseAgree X (typeBaseScope X β) c c') (T T' : FinProb X.ι)
    (hT : T = T') (drop : X.Name) (o : X.Tuple) :
    X.tupleRatio (b, Z) (c, W) β T drop o =
      X.tupleRatio (b', Z) (c', W) β T' drop o := by
  apply _root_.Lane_q_s06_loads.tupleRatio_congr_varVal X _ _ _ _ β T T' drop o
  · exact tagPost_congr_base X β β.obs Finset.Subset.rfl b b' Z hb
  · exact hT
  · exact reqNames_congr_base X β b b' Z hb
  · intro nm hnm
    exact reqNames_congr_base X β c c' W hc nm (Finset.mem_of_mem_erase hnm)

theorem locDensity_congr_base (s : X.State) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.locDensity (b, Z) (X.tgtName s) D ξ = X.locDensity (b', Z) (X.tgtName s) D ξ := by
  have hp := hb.withPar X (X.tgtName s) ξ
  have hprodA : (∏ u ∈ X.locBins D (X.tgtName s),
      (N : ℝ) * (X.candLaw (X.withPar b (X.tgtName s) ξ).1).w (b.2.1 u)) =
      ∏ u ∈ X.locBins D (X.tgtName s),
        (N : ℝ) * (X.candLaw (X.withPar b' (X.tgtName s) ξ).1).w (b'.2.1 u) := by
    apply Finset.prod_congr rfl
    intro u hu
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hu).1
    rw [hp.initial, hb.candidate k.1 (descBaseScope_key X s D k hk)]
  have hprodI : (∏ k ∈ X.locKeys D,
      safeRatio6 ((X.tagLawAt (X.parOf (X.withPar b (X.tgtName s) ξ)) k).w (b.2.2 k))
        (M.Λ (b.2.2 k))) =
      ∏ k ∈ X.locKeys D,
        safeRatio6 ((X.tagLawAt (X.parOf (X.withPar b' (X.tgtName s) ξ)) k).w (b'.2.2 k))
          (M.Λ (b'.2.2 k)) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hm := descBaseScope_key X s D k hk
    have hlaw : X.tagLawAt (X.parOf (X.withPar b (X.tgtName s) ξ)) k =
        X.tagLawAt (X.parOf (X.withPar b' (X.tgtName s) ξ)) k := by
      change X.tagLawAt ((X.withPar b (X.tgtName s) ξ).1, _) k = _
      rw [hp.initial]
      exact tagLawAt_bin_local X _ _ _ k (hp.candidate k.1 hm)
    rw [hlaw, hb.tag k hm]
  have hprodZ : (∏ ℓ ∈ X.locHid D,
      (N : ℝ) * (X.hidPost (X.withPar b (X.tgtName s) ξ) ℓ.1).w (Z ℓ)) =
      ∏ ℓ ∈ X.locHid D,
        (N : ℝ) * (X.hidPost (X.withPar b' (X.tgtName s) ξ) ℓ.1).w (Z ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hidPost_congr_base X ℓ.1 _ _ (hp.mono X (descBaseScope_obs X s D ℓ hℓ))]
  exact congrArg₂ (fun a z => a * z) (congrArg₂ (fun a i => a * i) hprodA hprodI) hprodZ

theorem s3Weight_congr_base (s : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N)
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.s3Weight (b, Z) s D o drop ξ = X.s3Weight (b', Z) s D o drop ξ := by
  cases hm : X.stMode s
  · have ht := hb.mono X (Finset.subset_union_left)
    have hprod : (∏ e ∈ D, if drop = some e then 1 else X.lowLik (b, Z) s ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.lowLik (b', Z) s ξ e.2 (o e) := by
      apply Finset.prod_congr rfl
      intro e he
      have hbβ := hb.mono X (descBaseScope_type X s D e he)
      have href : X.TβDel (b, Z) e.2 (X.tgt s) = X.TβDel (b', Z) e.2 (X.tgt s) :=
        tagPost_congr_base X e.2 _ (Finset.erase_subset _ _) b b' Z hbβ
      have hlik := tupleRatio_congr_base X e.2 b b' b b'
        (Function.update Z (X.tgt s) ξ) Z hbβ hbβ _ _ href
        (.hid (X.tgt s)) (o e)
      simp only [Ctx6.lowLik, Ctx6.withHid, hlik]
    simp only [Ctx6.s3Weight, hm, Ctx6.lowWeight, hprod,
      hidPost_congr_base X _ b b' ht, lowGate_congr_base X s D ξ b b' Z hb]
  · have hprod : (∏ e ∈ D, if drop = some e then 1 else X.highLik (b, Z) s ξ e.2 (o e)) =
        ∏ e ∈ D, if drop = some e then 1 else X.highLik (b', Z) s ξ e.2 (o e) := by
      apply Finset.prod_congr rfl
      intro e he
      have hbβ := hb.mono X (descBaseScope_type X s D e he)
      have hlik := tupleRatio_congr_base X e.2 _ _ b b' Z Z
        (hbβ.withPar X (X.tgtName s) ξ) hbβ (tagLaw6 M) (tagLaw6 M) rfl
        (.par (X.tgtName s)) (o e)
      simp only [Ctx6.highLik, Ctx6.withParH, hlik]
    have hprior : X.priorOf (b, Z) (X.tgtName s) = X.priorOf (b', Z) (X.tgtName s) := by
      cases X.tgtName s <;> simp [Ctx6.priorOf, hb.initial]
    simp only [Ctx6.s3Weight, hm, Ctx6.highWeight, hprod, hprior,
      highGate_congr_base X s D ξ b b' Z hb, locDensity_congr_base X s D ξ b b' Z hb]

theorem s3Fail_congr_base (s : X.State) (D : Finset (Id × X.Ty))
    (o : X.Data Id) (b b' : X.Base) (Z : X.Hid)
    (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.S3Fail (b, Z) s D o ↔ X.S3Fail (b', Z) s D o := by
  have hmass (drop : Option (Id × X.Ty)) : X.s3Mass (b, Z) s D o drop =
      X.s3Mass (b', Z) s D o drop :=
    Finset.sum_congr rfl (fun ξ _ => s3Weight_congr_base X s D o drop ξ b b' Z hb)
  have htrue : X.trueTarget (b, Z) s = X.trueTarget (b', Z) s := by
    cases hm : X.stMode s
    · simp [Ctx6.trueTarget, hm]
    · have hbin : (X.g.L.stKey s).1 ∈ descBaseScope X s D :=
        Finset.mem_union_left _ (bin_mem_posteriorScope X (X.tgt s).1)
      cases hf : (X.g.L.stKey s).2 <;>
        simp [Ctx6.trueTarget, hm, Ctx6.tgtName, primaryName6, hf, Ctx6.parOf,
          Par6.val, hb.initial, hb.candidate _ hbin]
  have hgate : X.S3TrueGate (b, Z) s D ↔ X.S3TrueGate (b', Z) s D := by
    cases hm : X.stMode s <;>
      simp only [Ctx6.S3TrueGate, hm, htrue,
        lowGate_congr_base X s D _ b b' Z hb, highGate_congr_base X s D _ b b' Z hb]
  simp only [Ctx6.S3Fail, hgate, Ctx6.S3Tests, hmass]

theorem rate3_congr_base (s : X.State) (D : Finset (Fin X.T × X.Ty))
    (b b' : X.Base) (Z : X.Hid) (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.rate3 (b, Z) s D = X.rate3 (b', Z) s D := by
  have hevent : (fun o : X.Data (Fin X.T) => X.S3Fail (b, Z) s D o) =
      (fun o : X.Data (Fin X.T) => X.S3Fail (b', Z) s D o) :=
    funext (fun o => propext (s3Fail_congr_base X s D o b b' Z hb))
  unfold Ctx6.rate3
  rw [hevent]
  apply Lane_q_s06_stages.pi_pr_eq_of_kernel_eq_on_depends _ _ D _
    (Lane_q_s06_stages.s3Fail_dependsOn_data X (b', Z) s D)
  intro e he
  exact tupleLaw_congr_base X e.2 b b' Z (hb.mono X (descBaseScope_type X s D e he))

theorem rate3Base_congr_base (s : X.State) (D : Finset (Fin X.T × X.Ty))
    (b b' : X.Base) (hb : BaseAgree X (descBaseScope X s D) b b') :
    X.rate3Base b s D = X.rate3Base b' s D := by
  have hevent : (fun Z : X.Hid => X.rate3 (b, Z) s D) =
      (fun Z : X.Hid => X.rate3 (b', Z) s D) :=
    funext (fun Z => rate3_congr_base X s D b b' Z hb)
  unfold Ctx6.rate3Base
  rw [hevent]
  apply pi_expect_congr_on _ _ (Lane_q_s06_stages.rate3HiddenScope X s D) _ (fun _ => X.y₀)
  · intro Z Z' hZ
    exact Lane_q_s06_stages.s3FailPr_eq_of_agree X b' s D Z Z' hZ
  · intro ℓ hℓ
    apply hidPost_congr_base X ℓ.1 b b'
    apply hb.mono X
    rcases Finset.mem_union.mp hℓ with hℓ | hℓ
    · exact descBaseScope_obs X s D ℓ hℓ
    · have heq : ℓ = X.tgt s := by
        by_cases hm : X.stMode s = .low
        · simpa [hm] using hℓ
        · simp [hm] at hℓ
      subst ℓ
      exact Finset.subset_union_left

/-- The exact union of coarse scopes consulted by a bin's three alarm branches. -/
def bad2BaseScope (w : X.Bin) : Finset X.Bin :=
  ((Finset.univ : Finset (CubeVertex n)).filter (fun x => (X.g.L.key x).1 = w)).biUnion
    (fun x => (X.C (X.g.L.key x)).biUnion (fun h => X.binsOf (X.C h))) ∪
  ((Finset.univ : Finset (CubeVertex n)).filter
    (fun x => IsEvenRole x ∧ (X.g.L.key x).1 = w)).biUnion
      (fun x => typeBaseScope X (X.evenType x)) ∪
  (X.g.L.oddStates.filter (fun s => (X.g.L.stKey s).1 = w)).biUnion
    (fun s => (X.absDescs s).biUnion (fun D => descBaseScope X s D))

theorem bad2BaseScope_step1 (w : X.Bin) (x : CubeVertex n)
    (hx : (X.g.L.key x).1 = w) (h : X.Key) (hh : h ∈ X.C (X.g.L.key x)) :
    X.binsOf (X.C h) ⊆ bad2BaseScope X w := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
      Finset.mem_biUnion.mpr ⟨h, hh, hu⟩⟩))

theorem bad2BaseScope_step2 (w : X.Bin) (x : CubeVertex n)
    (he : IsEvenRole x) (hx : (X.g.L.key x).1 = w) :
    typeBaseScope X (X.evenType x) ⊆ bad2BaseScope X w := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he, hx⟩, hu⟩))

theorem bad2BaseScope_step3 (w : X.Bin) (s : X.State) (hs : s ∈ X.g.L.oddStates)
    (hw : (X.g.L.stKey s).1 = w) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs s) :
    descBaseScope X s D ⊆ bad2BaseScope X w := by
  intro u hu
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨s, Finset.mem_filter.mpr ⟨hs, hw⟩, Finset.mem_biUnion.mpr ⟨D, hD, hu⟩⟩)

theorem bad2_congr_base (v : Fin N) (w : X.Bin) (c c' : X.Coarse)
    (hb : BaseAgree X (bad2BaseScope X w) (v, c) (v, c')) :
    X.Bad2 v w c ↔ X.Bad2 v w c' := by
  have hstep : ∀ x : CubeVertex n, (X.g.L.key x).1 = w →
      ∀ h ∈ X.C (X.g.L.key x), X.Step1OK (v, c) h ↔ X.Step1OK (v, c') h := by
    intro x hx h hh
    exact step1OK_congr_base X h _ _ (hb.mono X (bad2BaseScope_step1 X w x hx h hh))
  have hrate2 : ∀ x : CubeVertex n, IsEvenRole x → (X.g.L.key x).1 = w →
      X.rate2Base (v, c) (X.evenType x) = X.rate2Base (v, c') (X.evenType x) := by
    intro x he hx
    exact rate2Base_congr_base X _ _ _ (hb.mono X (bad2BaseScope_step2 X w x he hx))
  have hrate3 : ∀ s ∈ X.g.L.oddStates, (X.g.L.stKey s).1 = w →
      ∀ D ∈ X.absDescs s, X.rate3Base (v, c) s D = X.rate3Base (v, c') s D := by
    intro s hs hw D hD
    exact rate3Base_congr_base X s D _ _ (hb.mono X (bad2BaseScope_step3 X w s hs hw D hD))
  unfold Ctx6.Bad2
  constructor
  · rintro (⟨x, hx, h, hh, hfail⟩ | ⟨x, he, hx, hr⟩ | ⟨s, hs, hw, D, hD, hr⟩)
    · exact Or.inl ⟨x, hx, h, hh, fun hgood => hfail ((hstep x hx h hh).mpr hgood)⟩
    · exact Or.inr (Or.inl ⟨x, he, hx, (hrate2 x he hx) ▸ hr⟩)
    · exact Or.inr (Or.inr ⟨s, hs, hw, D, hD, (hrate3 s hs hw D hD) ▸ hr⟩)
  · rintro (⟨x, hx, h, hh, hfail⟩ | ⟨x, he, hx, hr⟩ | ⟨s, hs, hw, D, hD, hr⟩)
    · exact Or.inl ⟨x, hx, h, hh, fun hgood => hfail ((hstep x hx h hh).mp hgood)⟩
    · exact Or.inr (Or.inl ⟨x, he, hx, (hrate2 x he hx).symm ▸ hr⟩)
    · exact Or.inr (Or.inr ⟨s, hs, hw, D, hD, (hrate3 s hs hw D hD).symm ▸ hr⟩)

theorem bad2_depends_on_bins (v : Fin N) (w : X.Bin) :
    FinProb.DependsOn (fun z : X.Bin → BinData X =>
      X.Bad2 v w ((coarseBinEquiv X).symm z)) (bad2BaseScope X w) := by
  intro z z' hz
  apply propext
  apply bad2_congr_base X v w
  refine ⟨rfl, ?_, ?_⟩
  · intro u hu
    exact congrArg Prod.fst (hz u hu)
  · intro k hk
    exact congrArg (fun d : BinData X => d.2 k.2) (hz k.1 hk)

/-- Exact factorization against coarse avoidance constraints outside a function's bin scope. -/
theorem coarse_avoid_factor (v : Fin N) (S U : Finset X.Bin) (W : X.Coarse → ℝ)
    (hW : FinProb.DependsOn (fun z => W ((coarseBinEquiv X).symm z)) U)
    (hS : ∀ w ∈ S, Disjoint U (bad2BaseScope X w)) :
    (∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, (X.coarseLaw v).w c * W c) =
      (X.coarseLaw v).expect W * LocalLemma.mass (X.coarseLaw v).w
        (LocalLemma.avoid (X.bad2Set v) S) := by
  let E' (w : X.Bin) : Finset (X.Bin → BinData X) :=
    Finset.univ.filter (fun z => X.Bad2 v w ((coarseBinEquiv X).symm z))
  let P := FinProb.pi (binLaw X v)
  have hscope (w : X.Bin) (z z' : X.Bin → BinData X)
      (hz : ∀ u ∈ bad2BaseScope X w, z u = z' u) : z ∈ E' w ↔ z' ∈ E' w := by
    simpa only [E', Finset.mem_filter, Finset.mem_univ, true_and] using
      (Iff.of_eq (bad2_depends_on_bins X v w z z' hz))
  have hfactor := _root_.Lane_q_s06_loads.product_weight_avoid_factor
    (fun w a => (binLaw X v w).w a) (fun w a => (binLaw X v w).nonneg a)
    (fun w => (binLaw X v w).sum_eq_one) E' (bad2BaseScope X) hscope U
    (fun z => W ((coarseBinEquiv X).symm z)) hW S hS
  have hmem (z : X.Bin → BinData X) :
      z ∈ LocalLemma.avoid E' S ↔ (coarseBinEquiv X).symm z ∈ LocalLemma.avoid (X.bad2Set v) S := by
    simp [LocalLemma.avoid, E', Ctx6.bad2Set]
  have hsum (F : X.Coarse → ℝ) :
      (∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, (X.coarseLaw v).w c * F c) =
        ∑ z ∈ LocalLemma.avoid E' S, P.w z * F ((coarseBinEquiv X).symm z) := by
    have hfiltered : ∀ (Q : FinProb X.Coarse),
        (∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, Q.w c * F c) =
          Q.expect (fun c => if c ∈ LocalLemma.avoid (X.bad2Set v) S then F c else 0) := by
      intro Q
      simp [FinProb.expect, LocalLemma.avoid, Finset.sum_filter]
    rw [hfiltered, coarseLaw_expect X v]
    simp only [FinProb.expect, ← hmem]
    simp [P, LocalLemma.avoid, Finset.sum_filter]
  have hmass : LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) S) =
      LocalLemma.mass P.w (LocalLemma.avoid E' S) := by
    simpa [LocalLemma.mass] using hsum (fun _ => 1)
  rw [hsum, coarseLaw_expect X v W, hmass]
  exact hfactor

/-- Conditioning on all coarse alarms costs only the inverse charges of the touching alarms. -/
theorem stage2_expect_le_raw_of_local (v : Fin N) (S T U : Finset X.Bin)
    (hST : Disjoint S T) (hcover : S ∪ T = Finset.univ) (W : X.Coarse → ℝ)
    (hW0 : ∀ c, 0 ≤ W c)
    (hW : FinProb.DependsOn (fun z => W ((coarseBinEquiv X).symm z)) U)
    (hS : ∀ w ∈ S, Disjoint U (bad2BaseScope X w))
    (cert : AvoidCert6 (X.coarseLaw v).w (X.bad2Set v) ((n : ℝ) ^ (-(δ₁ / 8))))
    (hx : (n : ℝ) ^ (-(δ₁ / 8)) < 1) :
    (X.stage2Law v).expect W ≤
      (∏ w ∈ T, (1 - cert.x w))⁻¹ * (X.coarseLaw v).expect W := by
  have hpos := HypercubeRamsey.Lane_q_s06_loads.S06.AvoidCert6.mass_avoid_pos
    cert (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one hx
  have hmass : LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) Finset.univ) =
      (X.coarseLaw v).pr (fun c => ∀ w, ¬ X.Bad2 v w c) := by
    rw [Lane_q_s06_stages.avoid_mass_eq_pr]
    simp [Ctx6.bad2Set]
  have hgood : 0 < (X.coarseLaw v).pr (fun c => ∀ w, ¬ X.Bad2 v w c) := hmass ▸ hpos
  let p (w : X.Bin) : ℝ := cert.x w * ∏ j ∈ Finset.univ.filter (cert.adj w), (1 - cert.x j)
  have hav := LocalLemma.conditional_avoidance (X.coarseLaw v).w
    (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one (X.bad2Set v) cert.adj
    cert.adj_symm cert.adj_irrefl p cert.x cert.local_bound cert.x_nonneg
    (fun w => (cert.x_le w).trans_lt hx) (fun _ => le_rfl)
  have hcompare := hav.2.2.1 S T hST W hW0
  have hSpos := _root_.Lane_q_s06_loads.avoid_mass_positive_subset
    cert (X.coarseLaw v).nonneg (X.coarseLaw v).sum_eq_one hx S
  have hfactor := coarse_avoid_factor X v S U W hW hS
  have hratio : (∑ c ∈ LocalLemma.avoid (X.bad2Set v) S, (X.coarseLaw v).w c * W c) /
      LocalLemma.mass (X.coarseLaw v).w (LocalLemma.avoid (X.bad2Set v) S) =
        (X.coarseLaw v).expect W := by
    rw [hfactor]
    exact mul_div_cancel_right₀ _ (ne_of_gt hSpos)
  rw [hcover, hratio] at hcompare
  rw [Ctx6.stage2Law, Lane_q_s06_loads.restrictOr6_expect_formula _ _ _ hgood]
  -- Match the restriction formula's canonical decidability before comparing filtered sums.
  have hnum : (∑ c : X.Coarse,
      @ite ℝ (∀ w : X.Bin, ¬ X.Bad2 v w c) (Classical.propDecidable _)
        ((X.coarseLaw v).w c * W c) 0) =
      ∑ c ∈ LocalLemma.avoid (X.bad2Set v) Finset.univ, (X.coarseLaw v).w c * W c := by
    rw [LocalLemma.avoid, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hgoodc : ∀ w : X.Bin, ¬ X.Bad2 v w c <;>
      simp [Ctx6.bad2Set, hgoodc]
  rw [hnum, ← hmass]
  exact hcompare

/-- Alarms whose coarse input lists meet a given collection of target bins. -/
def touchingCoarse (U : Finset X.Bin) : Finset X.Bin :=
  Finset.univ.filter (fun w => ¬ Disjoint U (bad2BaseScope X w))

/-- Distinct interior bins retain their product moment bound, multiplied only by touching-alarm charges. -/
theorem interior_step1_product_stage2_le {R : Type*} [Fintype R] [DecidableEq R]
    (v : Fin N) (hv : v ∈ X.par.S₀) (s : Finset R) (h : R → X.Key)
    (hh : ∀ u, (h u).2 = .interior)
    (hsep : ∀ u ∈ s, ∀ u' ∈ s, u ≠ u' → (h u).1 ≠ (h u').1) (y : Fin N)
    (cert : AvoidCert6 (X.coarseLaw v).w (X.bad2Set v) ((n : ℝ) ^ (-(δ₁ / 8))))
    (hx : (n : ℝ) ^ (-(δ₁ / 8)) < 1) :
    (X.stage2Law v).expect (fun c => ∏ u ∈ s,
      (if X.Step1OK (v, c) (h u) then (N : ℝ) * (X.hidPost (v, c) (h u)).w y else 0)) ≤
        (∏ w ∈ touchingCoarse X (s.image (fun u => (h u).1)), (1 - cert.x w))⁻¹ *
          (20 * K) ^ s.card := by
  let U := s.image (fun u => (h u).1)
  let T := touchingCoarse X U
  let S := Finset.univ \ T
  let W (c : X.Coarse) : ℝ := ∏ u ∈ s,
    (if X.Step1OK (v, c) (h u) then (N : ℝ) * (X.hidPost (v, c) (h u)).w y else 0)
  have hW0 (c : X.Coarse) : 0 ≤ W c := by
    apply Finset.prod_nonneg
    intro u hu
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) ((X.hidPost _ _).nonneg y)
    · exact le_rfl
  have hW : FinProb.DependsOn (fun z => W ((coarseBinEquiv X).symm z)) U := by
    intro z z' hz
    apply Finset.prod_congr rfl
    intro u hu
    apply interior_step1_depends_on_bin X v (h u) (hh u) y
    intro w hw
    have heq : w = (h u).1 := Finset.mem_singleton.mp hw
    subst w
    exact hz _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
  have hST : Disjoint S T := Finset.sdiff_disjoint
  have hcover : S ∪ T = Finset.univ := by
    ext w
    simp [S]
  have hS : ∀ w ∈ S, Disjoint U (bad2BaseScope X w) := by
    intro w hw
    have hnot := (Finset.mem_sdiff.mp hw).2
    simpa [T, touchingCoarse] using hnot
  have hcompare := stage2_expect_le_raw_of_local X v S T U hST hcover W hW0 hW hS cert hx
  have hcharge : 0 ≤ (∏ w ∈ T, (1 - cert.x w))⁻¹ := by
    apply inv_nonneg.mpr
    apply Finset.prod_nonneg
    intro w hw
    exact sub_nonneg.mpr (le_of_lt ((cert.x_le w).trans_lt hx))
  exact hcompare.trans (mul_le_mul_of_nonneg_left
    (interior_step1_product_raw_le X v hv s h hh hsep y) hcharge)

/-- Padding key paths by self edges makes the fixed-radius balls monotone. -/
theorem keyBall_mono (root : X.Key) {r s : ℕ} (hrs : r ≤ s) :
    Lane_q_s06_loads.keyBall6 X root r ⊆ Lane_q_s06_loads.keyBall6 X root s := by
  induction s, hrs using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ s hrs ih =>
    intro k hk
    exact _root_.Lane_q_s06_loads.keyBall6_pad_self X root k s (ih hk)

theorem typeBaseScope_subset_ball (root : X.Key) (β : X.Ty)
    (hk : β.key ∈ Lane_q_s06_loads.keyBall6 X root 4)
    (hobs : ∀ ℓ ∈ β.obs, ℓ.1 ∈ Lane_q_s06_loads.keyBall6 X root 4) :
    typeBaseScope X β ⊆ X.binsOf (Lane_q_s06_loads.keyBall6 X root 5) := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hw
  · exact Finset.mem_image.mpr ⟨β.key, keyBall_mono X root (by omega) hk, rfl⟩
  · obtain ⟨ℓ, hℓ, hw⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨k,
      _root_.Lane_q_s06_loads.keyBall6_extend_C X root ℓ.1 k 4 (hobs ℓ hℓ) hk, rfl⟩

theorem evenTypeBaseScope_subset_ball (w : X.Bin) (x : CubeVertex n)
    (hx : (X.g.L.key x).1 = w) :
    typeBaseScope X (X.evenType x) ⊆
      X.binsOf (Lane_q_s06_loads.keyBall6 X (w, .interior) 5) := by
  let gr : X.Bin × CubeVertex X.m := (w, X.g.L.sign x)
  have hroot := _root_.Lane_q_s06_loads.keyBall6_contains_same_bin X gr (X.g.L.key x) hx
  apply typeBaseScope_subset_ball X (w, .interior) (X.evenType x)
  · have hkey : (X.evenType x).key = X.g.L.key x := by
      unfold Ctx6.evenType makeType6
      split_ifs <;> rfl
    rw [hkey]
    exact keyBall_mono X (w, .interior) (by omega) hroot
  · intro ℓ hℓ
    have hscope := _root_.Lane_q_s06_loads.evenType_obs_subset_bad3Scope X gr x hx rfl hℓ
    exact (Finset.mem_product.mp hscope).1

theorem descBaseScope_subset_ball (w : X.Bin) (s : X.State)
    (hw : (X.g.L.stKey s).1 = w) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs s) :
    descBaseScope X s D ⊆ X.binsOf (Lane_q_s06_loads.keyBall6 X (w, .interior) 5) := by
  let root : X.Key := (w, .interior)
  let gr : X.Bin × CubeVertex X.m := (w, X.g.L.stSign s)
  have hs1 := _root_.Lane_q_s06_loads.keyBall6_contains_same_bin X gr (X.g.L.stKey s) hw
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image.mpr ⟨k,
      _root_.Lane_q_s06_loads.keyBall6_extend_C X root (X.g.L.stKey s) k 4
        (keyBall_mono X root (by omega) hs1) hk, rfl⟩
  · obtain ⟨e, he, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨a, ha, htype⟩ := _root_.Lane_q_s06_loads.absDesc_type_mem_stNbr X s D hD e he
    have hka : X.g.L.stKey a ∈ X.C (X.g.L.stKey s) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, _root_.Lane_q_s06_loads.ctx6_stNbr_key_adjacent X s a ha⟩
    have ha2 := _root_.Lane_q_s06_loads.keyBall6_extend_C X root
      (X.g.L.stKey s) (X.g.L.stKey a) 1 hs1 hka
    apply typeBaseScope_subset_ball X root e.2 ?_ ?_ hu
    · have hkey : (X.stType a).key = X.g.L.stKey a := by
        unfold Ctx6.stType ChunkLayout6.stType makeType6
        split_ifs <;> rfl
      rw [htype, hkey]
      exact keyBall_mono X root (show 2 ≤ 4 by omega) ha2
    · intro ℓ hℓ
      have hscope := _root_.Lane_q_s06_loads.stType_obs_subset_bad3Scope X gr s a ha hw rfl
        (by simpa [htype] using hℓ)
      exact (Finset.mem_product.mp hscope).1

/-- All three coarse alarms are confined to a fixed grid neighbourhood. -/
theorem bad2BaseScope_subset_ball (w : X.Bin) :
    bad2BaseScope X w ⊆ X.binsOf (Lane_q_s06_loads.keyBall6 X (w, .interior) 5) := by
  let root : X.Key := (w, .interior)
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨x, hx, hu⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨h, hh, hu⟩ := Finset.mem_biUnion.mp hu
      have hxw := (Finset.mem_filter.mp hx).2
      let gr : X.Bin × CubeVertex X.m := (w, X.g.L.sign x)
      have hx1 := _root_.Lane_q_s06_loads.keyBall6_contains_same_bin X gr (X.g.L.key x) hxw
      have hh2 := _root_.Lane_q_s06_loads.keyBall6_extend_C X root (X.g.L.key x) h 1 hx1 hh
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
      have hk3 := _root_.Lane_q_s06_loads.keyBall6_extend_C X root h k 2 hh2 hk
      exact Finset.mem_image.mpr ⟨k, keyBall_mono X root (by omega) hk3, rfl⟩
    · obtain ⟨x, hx, hu⟩ := Finset.mem_biUnion.mp hu
      exact evenTypeBaseScope_subset_ball X w x (Finset.mem_filter.mp hx).2.2 hu
  · obtain ⟨s, hs, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨D, hD, hu⟩ := Finset.mem_biUnion.mp hu
    exact descBaseScope_subset_ball X w s (Finset.mem_filter.mp hs).2 D hD hu

theorem touchingCoarse_subset_ball (u : X.Bin) :
    touchingCoarse X {u} ⊆ X.binsOf (Lane_q_s06_loads.keyBall6 X (u, .interior) 6) := by
  intro w hw
  obtain ⟨v, hv, hvscope⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hw).2
  have hvu : v = u := Finset.mem_singleton.mp hv
  subst v
  obtain ⟨k, hk, hku⟩ := Finset.mem_image.mp (bad2BaseScope_subset_ball X w hvscope)
  have hback := _root_.Lane_q_s06_loads.keyBall6_symm X 5 (w, .interior) k hk
  let gr : X.Bin × CubeVertex X.m := (u, fun _ => false)
  have hk1 := _root_.Lane_q_s06_loads.keyBall6_contains_same_bin X gr k hku
  have hw6 := _root_.Lane_q_s06_loads.keyBall6_concat X 1 5
    (u, .interior) k (w, .interior) hk1 hback
  exact Finset.mem_image.mpr ⟨(w, .interior), hw6, rfl⟩

theorem touchingCoarse_singleton_card_le (u : X.Bin) :
    (touchingCoarse X {u}).card ≤ 602 ^ 6 := by
  calc
    _ ≤ (X.binsOf (Lane_q_s06_loads.keyBall6 X (u, .interior) 6)).card :=
      Finset.card_le_card (touchingCoarse_subset_ball X u)
    _ ≤ (Lane_q_s06_loads.keyBall6 X (u, .interior) 6).card := Finset.card_image_le
    _ ≤ 602 ^ 6 := Lane_q_s06_loads.keyBall6_card_le X (u, .interior) 6

theorem touchingCoarse_card_le (U : Finset X.Bin) :
    (touchingCoarse X U).card ≤ U.card * 602 ^ 6 := by
  have hsub : touchingCoarse X U ⊆ U.biUnion (fun u => touchingCoarse X {u}) := by
    intro w hw
    obtain ⟨u, hu, huscope⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hw).2
    exact Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.not_disjoint_iff.mpr ⟨u, Finset.mem_singleton_self _, huscope⟩⟩⟩
  calc
    _ ≤ (U.biUnion (fun u => touchingCoarse X {u})).card := Finset.card_le_card hsub
    _ ≤ ∑ u ∈ U, (touchingCoarse X {u}).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ U, 602 ^ 6 := Finset.sum_le_sum (fun u _ => touchingCoarse_singleton_card_le X u)
    _ = _ := by simp

/-- Restricting a cube vertex to a coordinate block preserves its count of ones on that block. -/
theorem boolWeight_restrict_eq (A : Finset (Fin n)) (x : CubeVertex n) :
    Lane_q_s06_front.boolWeight (fun a : {a : Fin n // a ∈ A} => x a.1) =
      (A.filter fun a => x a = true).card := by
  classical
  symm
  apply Finset.card_bij (fun a ha => ⟨a, (Finset.mem_filter.mp ha).1⟩)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a ha b hb hab
    exact congrArg Subtype.val hab
  · intro a ha
    exact ⟨a.1, Finset.mem_filter.mpr ⟨a.2, (Finset.mem_filter.mp ha).2⟩, rfl⟩

/-- Independent coarse blocks give the product of the individual bin-probability caps. -/
theorem coarseBin_fiber_fraction_le (L : ChunkLayout6 n) (w : BinVector6 n) :
    ((Finset.univ.filter fun x : CubeVertex n => L.coarseBin x = w).card : ℝ) /
      (2 : ℝ) ^ n ≤ (2 * (n : ℝ) ^ (-(1 / 25 : ℝ))) ^ coarseChunkCount := by
  classical
  let Coord (i : Fin coarseChunkCount) := {a : Fin n // a ∈ L.coarseChunks i}
  let events (i : Fin coarseChunkCount) : Finset (Coord i → Bool) :=
    Finset.univ.filter (fun f => L.bin i (Lane_q_s06_front.boolWeight f) = w i)
  have hCoordCard (i : Fin coarseChunkCount) :
      Fintype.card (Coord i) = (L.coarseChunks i).card := by
    simp [Coord, Fintype.card_coe]
  have hWeightBound (i : Fin coarseChunkCount) (f : Coord i → Bool) :
      Lane_q_s06_front.boolWeight f ≤ (L.coarseChunks i).card := by
    calc
      _ ≤ Fintype.card (Coord i) := Finset.card_filter_le _ _
      _ = _ := hCoordCard i
  have hLayer (i : Fin coarseChunkCount) (q : ℕ) :
      (Finset.univ.filter fun f : Coord i → Bool => Lane_q_s06_front.boolWeight f = q).card =
        Nat.choose (L.coarseChunks i).card q := by
    calc
      _ = Fintype.card {f : Coord i → Bool // Lane_q_s06_front.boolWeight f = q} := by
        symm
        exact Fintype.card_subtype _
      _ = Nat.choose (Fintype.card (Coord i)) q :=
        Lane_q_s06_front.boolWeightLayerCard (Coord i) q
      _ = _ := by rw [hCoordCard]
  have hLocal (i : Fin coarseChunkCount) :
      ((events i).card : ℝ) ≤
        (2 * (n : ℝ) ^ (-(1 / 25 : ℝ))) * (2 : ℝ) ^ (L.coarseChunks i).card := by
    let layer (q : ℕ) : Finset (Coord i → Bool) :=
      (Finset.univ.filter fun f => Lane_q_s06_front.boolWeight f = q).filter
        (fun _ => L.bin i q = w i)
    have hUnion : events i = (Finset.range ((L.coarseChunks i).card + 1)).biUnion layer := by
      ext f
      simp only [events, layer, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Finset.mem_range]
      constructor
      · intro hf
        exact ⟨Lane_q_s06_front.boolWeight f, Nat.lt_succ_of_le (hWeightBound i f), rfl, hf⟩
      · rintro ⟨q, hq, hweight, hbin⟩
        simpa [hweight] using hbin
    have hLayerCard (q : ℕ) : (layer q).card =
        if L.bin i q = w i then Nat.choose (L.coarseChunks i).card q else 0 := by
      by_cases hq : L.bin i q = w i <;> simp [layer, hq, hLayer]
    have hcardNat : (events i).card ≤
        ∑ q ∈ Finset.range ((L.coarseChunks i).card + 1), (layer q).card := by
      rw [hUnion]
      exact Finset.card_biUnion_le
    have hcardReal : ((events i).card : ℝ) ≤
        ∑ q ∈ Finset.range ((L.coarseChunks i).card + 1), ((layer q).card : ℝ) := by
      exact_mod_cast hcardNat
    calc
      _ ≤ ∑ q ∈ Finset.range ((L.coarseChunks i).card + 1), ((layer q).card : ℝ) := hcardReal
      _ = ∑ q ∈ Finset.range ((L.coarseChunks i).card + 1),
          if L.bin i q = w i then (Nat.choose (L.coarseChunks i).card q : ℝ) else 0 := by
        simp only [hLayerCard, Nat.cast_ite, Nat.cast_zero]
      _ ≤ _ := L.bin_probability i (w i)
  have hProduct := Lane_q_s06_front.cubeBlockEventFraction_le L.coarseChunks
    L.chunks_disjoint.1 Finset.univ events (2 * (n : ℝ) ^ (-(1 / 25 : ℝ)))
    (by positivity) (fun i _ => hLocal i)
  have hWeightEq (i : Fin coarseChunkCount) (x : CubeVertex n) :
      Lane_q_s06_front.boolWeight (fun a : Coord i => x a.1) = L.coarseCount x i :=
    boolWeight_restrict_eq (L.coarseChunks i) x
  have hEvent : (Finset.univ.filter fun x : CubeVertex n =>
      ∀ i ∈ (Finset.univ : Finset (Fin coarseChunkCount)),
        (fun a : Coord i => x a.1) ∈ events i) =
      Finset.univ.filter (fun x : CubeVertex n => L.coarseBin x = w) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, true_implies, events, hWeightEq]
    change (∀ i : Fin coarseChunkCount, L.coarseBin x i = w i) ↔ L.coarseBin x = w
    constructor
    · intro hx
      funext i
      exact hx i
    · intro hx i
      exact congrFun hx i
  rw [hEvent] at hProduct
  simpa only [Finset.card_univ, Fintype.card_fin] using hProduct

/-- The near relation required by the base moments: equal coarse-bin vectors. -/
def sameBinNear (L : ChunkLayout6 n) (u : CubeVertex n) : Finset (CubeVertex n) :=
  Finset.univ.filter (fun u' => L.coarseBin u' = L.coarseBin u)

theorem sameBinNear_card_le (L : ChunkLayout6 n) (u : CubeVertex n) :
    ((sameBinNear L u).card : ℝ) ≤
      (2 * (n : ℝ) ^ (-(1 / 25 : ℝ))) ^ coarseChunkCount * Fintype.card (CubeVertex n) := by
  have h := coarseBin_fiber_fraction_le L (L.coarseBin u)
  have hscaled := (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ n)).mp h
  simpa [sameBinNear, OAI.HypercubeRamsey.card_cubeVertex] using hscaled

/-- The repeated-bin contribution, including its Step 1 cap, vanishes in the n-th moment. -/
theorem sameBinNear_moment_eventually_small :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * (2 * (n : ℝ) ^ (-(1 / 25 : ℝ))) ^ coarseChunkCount * (n : ℝ) ^ d₁ ≤ 1 := by
  have hDecay : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-((11 : ℝ) - d₁)))
      Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num [d₁] : (0 : ℝ) < 11 - d₁)).comp
      tendsto_natCast_atTop_atTop
  have hlimit : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ coarseChunkCount *
      (n : ℝ) ^ (-((11 : ℝ) - d₁))) Filter.atTop (nhds 0) := by
    simpa using hDecay.const_mul ((2 : ℝ) ^ coarseChunkCount)
  filter_upwards [Filter.eventually_ge_atTop 1,
    hlimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hsmall
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hPow : ((n : ℝ) ^ (-(1 / 25 : ℝ))) ^ coarseChunkCount = (n : ℝ) ^ (-12 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnPos.le]
    congr 1
    norm_num [coarseChunkCount]
  have hEq : (n : ℝ) * (2 * (n : ℝ) ^ (-(1 / 25 : ℝ))) ^ coarseChunkCount * (n : ℝ) ^ d₁ =
      (2 : ℝ) ^ coarseChunkCount * (n : ℝ) ^ (-((11 : ℝ) - d₁)) := by
    rw [mul_pow, hPow]
    calc
      _ = (2 : ℝ) ^ coarseChunkCount *
          ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-12 : ℝ) * (n : ℝ) ^ d₁) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by
        rw [← Real.rpow_add hnPos, ← Real.rpow_add hnPos]
        congr 2
        ring
  rw [hEq]
  exact hsmall.le

end
end HypercubeRamsey.Lane_sol_s06_loadA
