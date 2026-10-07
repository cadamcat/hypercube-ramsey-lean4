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

end
end HypercubeRamsey.Lane_sol_s06_loadA
