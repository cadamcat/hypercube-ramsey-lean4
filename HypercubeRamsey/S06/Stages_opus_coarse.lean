import HypercubeRamsey.S06.Stages_sol_s06_hidden

/-!
# Coarse stage: the grouped future Step 2 and Step 3 alarms (L6.1h coarse, 06:472–496)

At a retained `V₀ = v` the coarse certificate needs, for every bin `w`, the probability over the raw coarse law
that some future Step 2 rate exceeds `n^{-δ₂u/8}` or some Step 3 rate exceeds `e^{-.0045k}` at a key of `w`.
Stage 1 (`V0Good v`) bounds the `V₀`-averages of all these rates; Markov turns each into one alarm bound.  The union
at a bin is not over all types or descriptors (there are `2^m` signs), but over their classes under the symmetry of
the hidden laws at a fixed base: `hidLaw base` is the product of `hidPost base ℓ.1` over hidden keys `ℓ`, so it is
invariant under every permutation of hidden keys that keeps `ℓ.1`, and the Step 2 and Step 3 failure events are
equivariant under such permutations (06:472–475, 06:488–496: "conditional future probabilities have the same sign
symmetry").  The frozen `RateShapes` predicate (equality of `V₀`-averaged rates) is not used.

* Step 2: the rate of a low type depends only on its key, severity and `|F|`; of a high type, on its key and
  whether its list is `{(h,t)}`.  Per bin: `4(m+1)` low and `4` high classes, total `≤ 8(m+1)n^{-δ₂/8}`.
* Step 3: the rate depends on the target key, mode and the descriptor translated to central sign `0`.  Near states
  (`j ≤ J+2`) land in Sol's code set at sign `0`; far-high states have empty observation lists.
-/

namespace HypercubeRamsey.S06.Lane_opus_coarse

open Classical HypercubeRamsey.S06 OAI.HypercubeRamsey
open HypercubeRamsey.Lane_sol_s06_hidden
open scoped BigOperators

noncomputable section

/-! ### Generic union and Markov bounds -/

/-- A union of events indexed by a finset, where events with the same code imply each other, costs one bound per
code in a covering code set. -/
theorem pr_exists_code_le {Ω ι κ : Type*} [Fintype Ω] [DecidableEq κ] (P : FinProb Ω)
    (S : Finset ι) (U : Finset κ) (code : ι → κ) (hU : ∀ x ∈ S, code x ∈ U)
    (A : ι → Ω → Prop) (bound : κ → ℝ) (hb0 : ∀ q ∈ U, 0 ≤ bound q)
    (hcls : ∀ x ∈ S, ∀ y ∈ S, code x = code y → ∀ ω, A x ω → A y ω)
    (hA : ∀ x ∈ S, P.pr (A x) ≤ bound (code x)) :
    P.pr (fun ω => ∃ x ∈ S, A x ω) ≤ ∑ q ∈ U, bound q := by
  let B : κ → Ω → Prop := fun q ω => ∃ x ∈ S, code x = q ∧ A x ω
  have hsub : ∀ ω, (∃ x ∈ S, A x ω) → ∃ q ∈ U, B q ω := by
    rintro ω ⟨x, hx, hAx⟩
    exact ⟨code x, hU x hx, x, hx, rfl, hAx⟩
  have hB : ∀ q ∈ U, P.pr (B q) ≤ bound q := by
    intro q hq
    by_cases hex : ∃ x ∈ S, code x = q
    · obtain ⟨x₀, hx₀, hq₀⟩ := hex
      calc
        P.pr (B q) ≤ P.pr (A x₀) := Lane_q_s06_stages.pr_mono P (by
          rintro ω ⟨x, hx, hxq, hAx⟩
          exact hcls x hx x₀ hx₀ (hxq.trans hq₀.symm) ω hAx)
        _ ≤ bound (code x₀) := hA x₀ hx₀
        _ = bound q := by rw [hq₀]
    · have hempty : ∀ ω, ¬ B q ω := by
        rintro ω ⟨x, hx, hxq, _⟩
        exact hex ⟨x, hx, hxq⟩
      have hzero : P.pr (B q) = 0 := by
        unfold FinProb.pr
        exact Finset.sum_eq_zero fun ω _ => if_neg (hempty ω)
      rw [hzero]
      exact hb0 q hq
  calc
    P.pr (fun ω => ∃ x ∈ S, A x ω) ≤ P.pr (fun ω => ∃ q ∈ U, B q ω) :=
      Lane_q_s06_stages.pr_mono P hsub
    _ ≤ ∑ q ∈ U, P.pr (B q) := pr_finite_union_le P U B
    _ ≤ ∑ q ∈ U, bound q := Finset.sum_le_sum hB

/-- Markov's inequality in the strict form used by the alarms. -/
theorem pr_lt_le_of_expect_le {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (t q : ℝ) (ht : 0 < t) (hq : P.expect f ≤ q) :
    P.pr (fun ω => t < f ω) ≤ q / t :=
  (Lane_q_s06_stages.pr_mono P (fun _ h => le_of_lt h)).trans
    ((FinProb.markov P f t hf ht).trans (div_le_div_of_nonneg_right hq ht.le))

theorem expect_nonneg' {Ω : Type*} [Fintype Ω] (P : FinProb Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ P.expect f := by
  unfold FinProb.expect
  exact Finset.sum_nonneg fun ω _ => mul_nonneg (P.nonneg ω) (hf ω)

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-! ### Key-preserving permutations of hidden keys (from the sol-s06-hidden draft, checked here) -/


def hiddenPermEquiv (e : Equiv.Perm X.HKey) : Equiv.Perm X.Hid :=
  e.arrowCongr (Equiv.refl (Fin N))

@[simp] theorem hiddenPermEquiv_apply (e : Equiv.Perm X.HKey) (Z : X.Hid) (ℓ : X.HKey) :
    hiddenPermEquiv X e Z ℓ = Z (e.symm ℓ) := rfl

theorem hidLaw_weight_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (Z : X.Hid) :
    (X.hidLaw base).w (hiddenPermEquiv X e Z) = (X.hidLaw base).w Z := by
  change (∏ ℓ, (X.hidPost base ℓ.1).w (Z (e.symm ℓ))) = ∏ ℓ, (X.hidPost base ℓ.1).w (Z ℓ)
  rw [← Equiv.prod_comp e]
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  rw [he ℓ, Equiv.symm_apply_apply]

theorem hidLaw_expect_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (F : X.Hid → ℝ) :
    (X.hidLaw base).expect F = (X.hidLaw base).expect (fun Z => F (hiddenPermEquiv X e Z)) := by
  unfold FinProb.expect
  calc
    _ = ∑ Z, (X.hidLaw base).w (hiddenPermEquiv X e Z) * F (hiddenPermEquiv X e Z) :=
      (Equiv.sum_comp (hiddenPermEquiv X e) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Z hZ
      rw [hidLaw_weight_hiddenPerm X base e he Z]

def renamedType (e : Equiv.Perm X.HKey) (β : X.Ty) : X.Ty :=
  (β.key, β.mode, β.2.2.1, β.obs.image e)

@[simp] theorem renamedType_key (e : Equiv.Perm X.HKey) (β : X.Ty) : (renamedType X e β).key = β.key := rfl
@[simp] theorem renamedType_mode (e : Equiv.Perm X.HKey) (β : X.Ty) : (renamedType X e β).mode = β.mode := rfl
@[simp] theorem renamedType_sev (e : Equiv.Perm X.HKey) (β : X.Ty) : (renamedType X e β).sev = β.sev := rfl
@[simp] theorem renamedType_obs (e : Equiv.Perm X.HKey) (β : X.Ty) : (renamedType X e β).obs = β.obs.image e := rfl
@[simp] theorem renamedType_u (e : Equiv.Perm X.HKey) (β : X.Ty) : (renamedType X e β).u = β.u := by
  cases hm : β.mode <;> simp [Type6.u, hm]

theorem renamedType_inverse (e : Equiv.Perm X.HKey) (β : X.Ty) :
    renamedType X e.symm (renamedType X e β) = β := by
  rcases β with ⟨h, mode, j, obs⟩
  change (h, mode, j, (obs.image e).image e.symm) = (h, mode, j, obs)
  rw [Finset.image_image]
  simp

def typePermEquiv (e : Equiv.Perm X.HKey) : Equiv.Perm X.Ty where
  toFun := renamedType X e
  invFun := renamedType X e.symm
  left_inv := renamedType_inverse X e
  right_inv := by intro β; simpa using renamedType_inverse X e.symm β

theorem tagGate_renamedType (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (i : X.ι) :
    X.tagGate base (renamedType X e β) i ↔ X.tagGate base β i := by
  unfold Ctx6.tagGate
  simp only [renamedType_key, renamedType_obs, Finset.forall_mem_image, he]

theorem tagWeight_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (obs : Finset X.HKey) (Z : X.Hid) (i : X.ι) :
    X.tagWeight (base, hiddenPermEquiv X e Z) (renamedType X e β) (obs.image e) i =
      X.tagWeight (base, Z) β obs i := by
  have hgate := propext (tagGate_renamedType X base e he β i)
  unfold Ctx6.tagWeight
  simp only [renamedType_key, hgate]
  congr 1
  rw [Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro ℓ hℓ
    simp only [he, hiddenPermEquiv_apply, Equiv.symm_apply_apply]
  · exact fun a _ b _ hab => e.injective hab

theorem tagMass_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (obs : Finset X.HKey) (Z : X.Hid) :
    X.tagMass (base, hiddenPermEquiv X e Z) (renamedType X e β) (obs.image e) =
      X.tagMass (base, Z) β obs := by
  apply Finset.sum_congr rfl
  intro i hi
  exact tagWeight_hiddenPerm X base e he β obs Z i

theorem step2Tests_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (Z : X.Hid) :
    X.Step2Tests (base, hiddenPermEquiv X e Z) (renamedType X e β) ↔ X.Step2Tests (base, Z) β := by
  have hfull := tagMass_hiddenPerm X base e he β β.obs Z
  have hdel : ∀ ℓ, X.tagMass (base, hiddenPermEquiv X e Z) (renamedType X e β)
      ((β.obs.image e).erase (e ℓ)) = X.tagMass (base, Z) β (β.obs.erase ℓ) := by
    intro ℓ
    rw [← Finset.image_erase e.injective]
    exact tagMass_hiddenPerm X base e he β (β.obs.erase ℓ) Z
  unfold Ctx6.Step2Tests Ctx6.step2Thr
  simp only [renamedType_obs, renamedType_u]
  rw [hfull]
  constructor
  · rintro ⟨hp, ht, hd⟩
    refine ⟨hp, ht, ?_⟩
    intro ℓ hℓ
    have hh := hd (e ℓ) (Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩)
    rw [hdel] at hh
    exact hh
  · rintro ⟨hp, ht, hd⟩
    refine ⟨hp, ht, ?_⟩
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨k, hk, rfl⟩
    rw [hdel]
    exact hd k hk

theorem step2Fail_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (Z : X.Hid) :
    X.Step2Fail (base, hiddenPermEquiv X e Z) (renamedType X e β) ↔ X.Step2Fail (base, Z) β := by
  unfold Ctx6.Step2Fail
  simp only [renamedType_key]
  exact and_congr (tagGate_renamedType X base e he β _) (not_congr (step2Tests_hiddenPerm X base e he β Z))

theorem step2_base_rate_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) :
    (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (renamedType X e β)) =
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) β) := by
  let F : X.Hid → ℝ := fun Z => if X.Step2Fail (base, Z) (renamedType X e β) then 1 else 0
  calc
    _ = (X.hidLaw base).expect F := Lane_q_s06_stages.finprob_pr_eq_expect_indicator _ _
    _ = (X.hidLaw base).expect (fun Z => F (hiddenPermEquiv X e Z)) := hidLaw_expect_hiddenPerm X base e he F
    _ = _ := by
      rw [Lane_q_s06_stages.finprob_pr_eq_expect_indicator]
      apply Finset.sum_congr rfl
      intro Z hZ
      have hp := propext (step2Fail_hiddenPerm X base e he β Z)
      simp only [F, hp]

private theorem exists_perm_finset_image {A : Type*} [Fintype A] [DecidableEq A]
    (S T : Finset A) (hc : S.card = T.card) : ∃ e : Equiv.Perm A, S.image e = T := by
  let q : S ≃ T := Fintype.equivOfCardEq (by simpa using hc)
  let f : S → A := Subtype.val
  let g : S → A := fun s => (q s).val
  have hf : Function.Injective f := Subtype.val_injective
  have hg : Function.Injective g := fun a b hab => q.injective (Subtype.ext hab)
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨e, ?_⟩
  ext t
  constructor
  · rintro ht
    rcases Finset.mem_image.mp ht with ⟨s, hs, rfl⟩
    have heq : e s = (q ⟨s, hs⟩).val := he ⟨s, hs⟩
    rw [heq]
    exact (q ⟨s, hs⟩).property
  · intro ht
    let s := q.symm ⟨t, ht⟩
    refine Finset.mem_image.mpr ⟨s.val, s.property, ?_⟩
    simpa [f, g, s] using he s

def observationSigns (β : X.Ty) (k : X.Key) : Finset (CubeVertex X.m) :=
  (β.obs.filter fun ℓ => ℓ.1 = k).image Prod.snd

theorem mem_observationSigns (β : X.Ty) (k : X.Key) (t : CubeVertex X.m) :
    t ∈ observationSigns X β k ↔ (k, t) ∈ β.obs := by
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨ℓ, hℓ, ht⟩
    obtain ⟨hobs, hk⟩ := Finset.mem_filter.mp hℓ
    have heq : ℓ = (k, t) := Prod.ext hk ht
    exact heq ▸ hobs
  · intro ht
    exact Finset.mem_image.mpr ⟨(k, t), Finset.mem_filter.mpr ⟨ht, rfl⟩, rfl⟩

theorem exists_key_preserving_observation_perm (β β' : X.Ty)
    (hcard : ∀ k, (observationSigns X β k).card = (observationSigns X β' k).card) :
    ∃ e : Equiv.Perm X.HKey, (∀ ℓ, (e ℓ).1 = ℓ.1) ∧ β.obs.image e = β'.obs := by
  have hex : ∀ k : X.Key, ∃ p : Equiv.Perm (CubeVertex X.m),
      (observationSigns X β k).image p = observationSigns X β' k :=
    fun k => exists_perm_finset_image _ _ (hcard k)
  choose p hp using hex
  let e : Equiv.Perm X.HKey := {
    toFun := fun ℓ => (ℓ.1, p ℓ.1 ℓ.2)
    invFun := fun ℓ => (ℓ.1, (p ℓ.1).symm ℓ.2)
    left_inv := by intro ℓ; exact Prod.ext rfl ((p ℓ.1).symm_apply_apply ℓ.2)
    right_inv := by intro ℓ; exact Prod.ext rfl ((p ℓ.1).apply_symm_apply ℓ.2) }
  refine ⟨e, fun _ => rfl, ?_⟩
  ext ℓ
  constructor
  · rintro hℓ
    rcases Finset.mem_image.mp hℓ with ⟨k, hk, rfl⟩
    have hs : k.2 ∈ observationSigns X β k.1 := (mem_observationSigns X β k.1 k.2).mpr hk
    have ht : p k.1 k.2 ∈ observationSigns X β' k.1 := by
      rw [← hp k.1]
      exact Finset.mem_image.mpr ⟨k.2, hs, rfl⟩
    exact (mem_observationSigns X β' k.1 (p k.1 k.2)).mp ht
  · intro hℓ
    have ht := (mem_observationSigns X β' ℓ.1 ℓ.2).mpr hℓ
    rw [← hp ℓ.1] at ht
    rcases Finset.mem_image.mp ht with ⟨t, ht, heq⟩
    refine Finset.mem_image.mpr ⟨(ℓ.1, t), (mem_observationSigns X β ℓ.1 t).mp ht, ?_⟩
    exact Prod.ext rfl heq

theorem step2_base_rate_eq_of_observation_profile (base : X.Base) (β β' : X.Ty)
    (hkey : β.key = β'.key) (hmode : β.mode = β'.mode) (hsev : β.sev = β'.sev)
    (hcard : ∀ k, (observationSigns X β k).card = (observationSigns X β' k).card) :
    (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) β) =
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) β') := by
  obtain ⟨e, he, hobs⟩ := exists_key_preserving_observation_perm X β β' hcard
  have hβ : renamedType X e β = β' :=
    Prod.ext hkey (Prod.ext hmode (Prod.ext (Fin.ext hsev) hobs))
  have hh := step2_base_rate_hiddenPerm X base e he β
  rw [hβ] at hh
  exact hh.symm

theorem flip_signs_injective {m : ℕ} (t : CubeVertex m) : Function.Injective (flipVertex6 t) := by
  intro i j hij
  by_contra hne
  have hcoord := congrArg (fun s : CubeVertex m => s i) hij
  simp only [flipVertex6, Function.update_self, Function.update_of_ne hne] at hcoord
  cases hi : t i <;> simp_all

theorem central_sign_not_flip {m : ℕ} (t : CubeVertex m) (i : Fin m) : flipVertex6 t i ≠ t := by
  intro heq
  have hh := congrArg (fun s : CubeVertex m => s i) heq
  simp only [flipVertex6, Function.update_self] at hh
  cases hi : t i <;> simp_all

theorem central_flips_card {m : ℕ} (t : CubeVertex m) (F : Finset (Fin m)) :
    (insert t (F.image (flipVertex6 t))).card = F.card + 1 := by
  have hnot : t ∉ F.image (flipVertex6 t) := by
    intro ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, heq⟩
    exact central_sign_not_flip t i heq
  rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ (flip_signs_injective t)]

private theorem mem_lowObservations_iff {W : Type*} [Fintype W] {m : ℕ}
    (R : W → W → Prop) (h : CoarseKey6 W) (t : CubeVertex m) (F : Finset (Fin m)) (ℓ : HiddenKey6 W m) :
    ℓ ∈ lowObservations6 R h t F ↔
      (∃ k ∈ keyNeighborhood6 R h, (k, t) = ℓ) ∨ ∃ i ∈ F, (h, flipVertex6 t i) = ℓ := by
  classical
  simp only [lowObservations6, Finset.mem_union, Finset.mem_image, flipVertex6]

theorem low_observation_sign_set (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (k : X.Key) :
    ((lowObservations6 binAdjacent6 h t F).filter fun ℓ => ℓ.1 = k).image Prod.snd =
      if k = h then insert t (F.image (flipVertex6 t)) else if k ∈ X.C h then {t} else ∅ := by
  have hself : h ∈ X.C h := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
  ext s
  by_cases hkh : k = h
  · subst k
    simp only [if_pos rfl]
    constructor
    · intro hs
      rcases Finset.mem_image.mp hs with ⟨ℓ, hℓ, hs⟩
      obtain ⟨hobs, hk⟩ := Finset.mem_filter.mp hℓ
      rcases (mem_lowObservations_iff binAdjacent6 h t F ℓ).mp hobs with ⟨a, ha, rfl⟩ | ⟨i, hi, rfl⟩
      · exact Finset.mem_insert.mpr (Or.inl hs.symm)
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, hs⟩)
    · intro hs
      rcases Finset.mem_insert.mp hs with hs | hs
      · subst s
        refine Finset.mem_image.mpr ⟨(h, t), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
        exact (mem_lowObservations_iff binAdjacent6 h t F (h, t)).mpr (Or.inl ⟨h, hself, rfl⟩)
      · rcases Finset.mem_image.mp hs with ⟨i, hi, rfl⟩
        refine Finset.mem_image.mpr ⟨(h, flipVertex6 t i), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
        exact (mem_lowObservations_iff binAdjacent6 h t F _).mpr (Or.inr ⟨i, hi, rfl⟩)
  · simp only [if_neg hkh]
    by_cases hkC : k ∈ X.C h
    · simp only [if_pos hkC]
      constructor
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨ℓ, hℓ, hs⟩
        obtain ⟨hobs, hk⟩ := Finset.mem_filter.mp hℓ
        rcases (mem_lowObservations_iff binAdjacent6 h t F ℓ).mp hobs with ⟨a, ha, rfl⟩ | ⟨i, hi, rfl⟩
        · exact Finset.mem_singleton.mpr hs.symm
        · exact False.elim (hkh hk.symm)
      · intro hs
        have hst : s = t := Finset.mem_singleton.mp hs
        subst s
        refine Finset.mem_image.mpr ⟨(k, t), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
        exact (mem_lowObservations_iff binAdjacent6 h t F _).mpr (Or.inl ⟨k, hkC, rfl⟩)
    · simp only [if_neg hkC]
      constructor
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨ℓ, hℓ, hs⟩
        obtain ⟨hobs, hk⟩ := Finset.mem_filter.mp hℓ
        rcases (mem_lowObservations_iff binAdjacent6 h t F ℓ).mp hobs with ⟨a, ha, rfl⟩ | ⟨i, hi, rfl⟩
        · exact False.elim (hkC (hk ▸ ha))
        · exact False.elim (hkh hk.symm)
      · intro hs
        exact False.elim (Finset.notMem_empty _ hs)

theorem low_observation_profile_card (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (k : X.Key) :
    (((lowObservations6 binAdjacent6 h t F).filter fun ℓ => ℓ.1 = k).image Prod.snd).card =
      if k = h then F.card + 1 else if k ∈ X.C h then 1 else 0 := by
  rw [low_observation_sign_set X h t F k]
  split_ifs with hk hkC
  · exact central_flips_card t F
  · exact Finset.card_singleton _
  · rfl

theorem low_type_rate_eq_of_card (base : X.Base) (h : X.Key) (t t' : CubeVertex X.m)
    (F F' : Finset (Fin X.m)) (j : ℕ) (hj : j ≤ X.J) (hF : F.card = F'.card) :
    (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (makeType6 binAdjacent6 h t F j X.J)) =
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (makeType6 binAdjacent6 h t' F' j X.J)) := by
  apply step2_base_rate_eq_of_observation_profile X base
  · simp only [makeType6, if_pos hj, Type6.key]
  · simp only [makeType6, if_pos hj, Type6.mode]
  · simp only [makeType6, if_pos hj, Type6.sev]
  · intro k
    change (observationSigns X (makeType6 binAdjacent6 h t F j X.J) k).card =
      (observationSigns X (makeType6 binAdjacent6 h t' F' j X.J) k).card
    simp only [observationSigns, makeType6, if_pos hj, Type6.obs]
    have hleft := low_observation_profile_card X h t F k
    have hright := low_observation_profile_card X h t' F' k
    exact hleft.trans (by rw [hF]; exact hright.symm)

private theorem singleton_observation_card {A B : Type*} [DecidableEq A] [DecidableEq B]
    (h k : A) (t : B) :
    ((({(h, t)} : Finset (A × B)).filter fun z => z.1 = k).image Prod.snd).card =
      if h = k then 1 else 0 := by
  by_cases hk : h = k
  · subst hk
    have hset : ((({(h, t)} : Finset (A × B)).filter fun z => z.1 = h).image Prod.snd) = {t} := by
      ext s
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨z, ⟨rfl, _⟩, rfl⟩
        rfl
      · rintro rfl
        exact ⟨(h, s), ⟨rfl, rfl⟩, rfl⟩
    rw [hset, if_pos rfl, Finset.card_singleton]
  · have hset : (({(h, t)} : Finset (A × B)).filter fun z => z.1 = k) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact hk
    rw [hset, Finset.image_empty, Finset.card_empty, if_neg hk]

theorem high_type_rate_eq_of_option (base : X.Base) (h : X.Key) (t t' : CubeVertex X.m)
    (F F' : Finset (Fin X.m)) (j j' : ℕ) (hj : ¬ j ≤ X.J) (hj' : ¬ j' ≤ X.J)
    (hoption : (j = X.J + 1) ↔ (j' = X.J + 1)) :
    (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (makeType6 binAdjacent6 h t F j X.J)) =
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (makeType6 binAdjacent6 h t' F' j' X.J)) := by
  apply step2_base_rate_eq_of_observation_profile X base
  · simp only [makeType6, if_neg hj, if_neg hj', Type6.key]
  · simp only [makeType6, if_neg hj, if_neg hj', Type6.mode]
  · simp only [makeType6, if_neg hj, if_neg hj', Type6.sev]
  · intro k
    simp only [observationSigns, makeType6, if_neg hj, if_neg hj', Type6.obs, highObservations6]
    by_cases ho : j = X.J + 1
    · have ho' := hoption.mp ho
      simp only [if_pos ho, if_pos ho']
      exact (singleton_observation_card h k t).trans (singleton_observation_card h k t').symm

    · have ho' : j' ≠ X.J + 1 := fun hh => ho (hoption.mpr hh)
      by_cases hk : h = k <;> simp [ho, ho', hk]

theorem tagPost_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (obs : Finset X.HKey) (Z : X.Hid) :
    X.tagPost (base, hiddenPermEquiv X e Z) (renamedType X e β) (obs.image e) =
      X.tagPost (base, Z) β obs := by
  unfold Ctx6.tagPost
  congr 1
  funext i
  exact tagWeight_hiddenPerm X base e he β obs Z i

theorem Tβ_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (Z : X.Hid) :
    X.Tβ (base, hiddenPermEquiv X e Z) (renamedType X e β) = X.Tβ (base, Z) β :=
  tagPost_hiddenPerm X base e he β β.obs Z

theorem TβDel_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (Z : X.Hid) (ℓ : X.HKey) :
    X.TβDel (base, hiddenPermEquiv X e Z) (renamedType X e β) (e ℓ) = X.TβDel (base, Z) β ℓ := by
  unfold Ctx6.TβDel
  rw [renamedType_obs, ← Finset.image_erase e.injective]
  exact tagPost_hiddenPerm X base e he β (β.obs.erase ℓ) Z


def nameMap (e : Equiv.Perm X.HKey) : X.Name → X.Name
  | .par p => .par p
  | .hid ℓ => .hid (e ℓ)

theorem nameMap_symm (e : Equiv.Perm X.HKey) (nm : X.Name) : nameMap X e.symm (nameMap X e nm) = nm := by
  cases nm with
  | par p => rfl
  | hid ℓ => exact congrArg VarName6.hid (e.symm_apply_apply ℓ)

def namePermEquiv (e : Equiv.Perm X.HKey) : Equiv.Perm X.Name where
  toFun := nameMap X e
  invFun := nameMap X e.symm
  left_inv := nameMap_symm X e
  right_inv := by intro nm; simpa using nameMap_symm X e.symm nm

@[simp] theorem namePermEquiv_par (e : Equiv.Perm X.HKey) (p : ParentName6 X.Bin) :
    namePermEquiv X e (.par p) = .par p := rfl

@[simp] theorem namePermEquiv_hid (e : Equiv.Perm X.HKey) (ℓ : X.HKey) :
    namePermEquiv X e (.hid ℓ) = .hid (e ℓ) := rfl

theorem varVal_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey) (Z : X.Hid) (nm : X.Name) :
    X.varVal (base, hiddenPermEquiv X e Z) (namePermEquiv X e nm) = X.varVal (base, Z) nm := by
  cases nm with
  | par p => rfl
  | hid ℓ =>
    show Z (e.symm (e ℓ)) = Z ℓ
    rw [Equiv.symm_apply_apply]

private theorem reqNames_mem_iff {W : Type*} {m : ℕ} (β : Type6 W m) (nm : VarName6 W m) :
    nm ∈ reqNames6 β ↔ nm = .par (primaryName6 β.key) ∨
      (∃ ℓ ∈ β.obs, VarName6.hid ℓ = nm) ∨ (β.mode = .high ∧ nm = .par (otherPrimaryName6 β.key)) := by
  classical
  unfold reqNames6
  by_cases hm : β.mode = .high
  · rw [if_pos hm]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hm, h⟩)
    · rintro (h | h | ⟨_, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · rw [if_neg hm]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_image, Finset.notMem_empty, or_false]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rintro (h | h | ⟨hh, _⟩)
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hh hm

theorem reqNames_renamedType (e : Equiv.Perm X.HKey) (β : X.Ty) :
    reqNames6 (renamedType X e β) = (reqNames6 β).image (namePermEquiv X e) := by
  have hmem : ∀ nm : X.Name,
      namePermEquiv X e nm ∈ reqNames6 (renamedType X e β) ↔ nm ∈ reqNames6 β := by
    intro nm
    rw [reqNames_mem_iff, reqNames_mem_iff]
    cases nm with
    | par p =>
      simp only [namePermEquiv_par, renamedType_key, renamedType_mode, renamedType_obs]
      constructor
      · rintro (h | ⟨ℓ, _, h⟩ | h)
        · exact Or.inl h
        · cases h
        · exact Or.inr (Or.inr h)
      · rintro (h | ⟨ℓ, _, h⟩ | h)
        · exact Or.inl h
        · cases h
        · exact Or.inr (Or.inr h)
    | hid ℓ =>
      simp only [namePermEquiv_hid, renamedType_key, renamedType_mode, renamedType_obs]
      constructor
      · rintro (h | ⟨ℓ', hℓ', h⟩ | ⟨_, h⟩)
        · cases h
        · rcases Finset.mem_image.mp hℓ' with ⟨k, hk, rfl⟩
          injection h with h
          exact Or.inr (Or.inl ⟨k, hk, by rw [e.injective h]⟩)
        · cases h
      · rintro (h | ⟨ℓ', hℓ', h⟩ | ⟨_, h⟩)
        · cases h
        · injection h with h
          exact Or.inr (Or.inl ⟨e ℓ', Finset.mem_image_of_mem e hℓ', by rw [h]⟩)
        · cases h
  ext nm
  constructor
  · intro hnm
    let a := (namePermEquiv X e).symm nm
    have ha : namePermEquiv X e a ∈ reqNames6 (renamedType X e β) := by
      simpa [a] using hnm
    exact Finset.mem_image.mpr ⟨a, (hmem a).mp ha, (namePermEquiv X e).apply_symm_apply nm⟩
  · intro hnm
    rcases Finset.mem_image.mp hnm with ⟨a, ha, rfl⟩
    exact (hmem a).mpr ha

theorem labelLaw_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey) (Z : X.Hid)
    (names : Finset X.Name) (i : X.ι) :
    X.labelLaw (base, hiddenPermEquiv X e Z) (names.image (namePermEquiv X e)) i =
      X.labelLaw (base, Z) names i := by
  have hreq : X.reqNbhd (base, hiddenPermEquiv X e Z) (names.image (namePermEquiv X e)) =
      X.reqNbhd (base, Z) names := by
    ext y
    simp only [Ctx6.reqNbhd, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_image, varVal_hiddenPerm]
  unfold Ctx6.labelLaw
  rw [hreq]

theorem tupleLaw_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey)
    (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (β : X.Ty) (Z : X.Hid) :
    X.tupleLaw (base, hiddenPermEquiv X e Z) (renamedType X e β) = X.tupleLaw (base, Z) β := by
  have htag := Tβ_hiddenPerm X base e he β Z
  have hlabel : ∀ i, X.labelLaw (base, hiddenPermEquiv X e Z) (reqNames6 (renamedType X e β)) i =
      X.labelLaw (base, Z) (reqNames6 β) i := by
    intro i
    rw [reqNames_renamedType]
    exact labelLaw_hiddenPerm X base e Z (reqNames6 β) i
  unfold Ctx6.tupleLaw Ctx6.tupleLawOn
  rw [htag]
  congr 1
  funext i
  congr 1
  funext r
  exact hlabel i

/-! ### Step 2: the coarse future alarm union at a bin -/

theorem evenType_eq (x : CubeVertex n) :
    X.evenType x = makeType6 binAdjacent6 (X.g.L.key x) (X.g.L.sign x) (X.g.L.flippable x)
      (X.g.L.severity x) X.J := rfl

/-- At a fixed base, the Step 2 rate of a low even type depends only on its key, severity and `|F|`. -/
theorem low_step2_rate_eq (x x' : CubeVertex n) (hx : X.g.L.severity x ≤ X.J)
    (hkey : X.g.L.key x = X.g.L.key x') (hsev : X.g.L.severity x = X.g.L.severity x')
    (hF : (X.g.L.flippable x).card = (X.g.L.flippable x').card) (base : X.Base) :
    (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x)) =
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x')) := by
  rw [evenType_eq, evenType_eq, ← hkey, ← hsev]
  exact low_type_rate_eq_of_card X base _ _ _ _ _ _ hx hF

/-- At a fixed base, the Step 2 rate of a high even type depends only on its key and whether `j = J+1`. -/
theorem high_step2_rate_eq (x x' : CubeVertex n) (hx : ¬ X.g.L.severity x ≤ X.J)
    (hx' : ¬ X.g.L.severity x' ≤ X.J) (hkey : X.g.L.key x = X.g.L.key x')
    (hopt : X.g.L.severity x = X.J + 1 ↔ X.g.L.severity x' = X.J + 1) (base : X.Base) :
    (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x)) =
      (X.hidLaw base).pr (fun Z => X.Step2Fail (base, Z) (X.evenType x')) := by
  rw [evenType_eq, evenType_eq, ← hkey]
  exact high_type_rate_eq_of_option X base _ _ _ _ _ _ _ hx hx' hopt

/-- The two keys at a bin. -/
def keysAt (i : X.Bin) : Finset X.Key := Finset.univ.image fun f : KeyFlag6 => (i, f)

theorem keysAt_card_le (i : X.Bin) : (keysAt X i).card ≤ 2 := by
  have hflag : Fintype.card KeyFlag6 = 2 := by decide
  exact Finset.card_image_le.trans (by simp [hflag])

theorem mem_keysAt (h : X.Key) (i : X.Bin) (hi : h.1 = i) : h ∈ keysAt X i :=
  Finset.mem_image.mpr ⟨h.2, Finset.mem_univ _, Prod.ext hi.symm rfl⟩

/-- The grouped future Step 2 alarms at a bin (06:488–496), from the stage 1 bounds by Markov and the union over
the rate classes at a fixed base. -/
theorem coarse_step2_alarm_probability (v : Fin N) (i : X.Bin) (hn1 : 1 < (n : ℝ))
    (hr : (n : ℝ) ^ (-(δ₂ / 8)) ≤ 1 / 2)
    (hmean : ∀ x : CubeVertex n, IsEvenRole x → (X.g.L.key x).1 = i →
      (X.coarseLaw v).expect (fun c => (X.hidLaw (v, c)).pr fun Z => X.Step2Fail ((v, c), Z) (X.evenType x)) ≤
        (n : ℝ) ^ (-(δ₂ * (X.evenType x).u / 4))) :
    (X.coarseLaw v).pr (fun c => ∃ x : CubeVertex n, IsEvenRole x ∧ (X.g.L.key x).1 = i ∧
        (n : ℝ) ^ (-(δ₂ * (X.evenType x).u / 8)) <
          (X.hidLaw (v, c)).pr fun Z => X.Step2Fail ((v, c), Z) (X.evenType x)) ≤
      8 * ((X.m : ℝ) + 1) * (n : ℝ) ^ (-(δ₂ / 8)) := by
  have hn0 : 0 < (n : ℝ) := by linarith
  set r : ℝ := (n : ℝ) ^ (-(δ₂ / 8)) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos hn0 _
  have hpow8 : ∀ u : ℕ, (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 8)) = r ^ u := by
    intro u
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hpow4 : ∀ u : ℕ, (n : ℝ) ^ (-(δ₂ * (u : ℝ) / 4)) = (r ^ u) ^ 2 := by
    intro u
    rw [← hpow8, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  let R : CubeVertex n → X.Coarse → ℝ := fun x c =>
    (X.hidLaw (v, c)).pr fun Z => X.Step2Fail ((v, c), Z) (X.evenType x)
  let alarm : CubeVertex n → X.Coarse → Prop := fun x c => r ^ (X.evenType x).u < R x c
  have halarm_eq : ∀ x c, ((n : ℝ) ^ (-(δ₂ * (X.evenType x).u / 8)) < R x c) ↔ alarm x c := by
    intro x c
    rw [hpow8]
  have hx_alarm : ∀ x, IsEvenRole x → (X.g.L.key x).1 = i →
      (X.coarseLaw v).pr (alarm x) ≤ r ^ (X.evenType x).u := by
    intro x hx hxi
    have hm := hmean x hx hxi
    rw [hpow4] at hm
    have hpos : 0 < r ^ (X.evenType x).u := pow_pos hr0 _
    have h := pr_lt_le_of_expect_le (X.coarseLaw v) (R x) (fun c => Lane_q_s06_stages.pr_nonneg _ _)
      _ _ hpos hm
    have hdiv : (r ^ (X.evenType x).u) ^ 2 / r ^ (X.evenType x).u = r ^ (X.evenType x).u := by
      rw [pow_two, mul_div_assoc, div_self hpos.ne', mul_one]
    rw [hdiv] at h
    exact h
  -- low types
  let Slow : Finset (CubeVertex n) := Finset.univ.filter fun x =>
    IsEvenRole x ∧ (X.g.L.key x).1 = i ∧ X.g.L.severity x ≤ X.J
  let Ulow : Finset (X.Key × ℕ × ℕ) :=
    keysAt X i ×ˢ (Finset.range (X.J + 1) ×ˢ Finset.range (X.g.L.m + 1))
  have hlow : (X.coarseLaw v).pr (fun c => ∃ x ∈ Slow, alarm x c) ≤ 4 * ((X.m : ℝ) + 1) * r := by
    have hmain := pr_exists_code_le (X.coarseLaw v) Slow Ulow
      (fun x => (X.g.L.key x, X.g.L.severity x, (X.g.L.flippable x).card))
      (by
        intro x hx
        obtain ⟨_, hxi, hxJ⟩ := (Finset.mem_filter.mp hx).2
        refine Finset.mem_product.mpr ⟨mem_keysAt X _ i hxi, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hxJ)
        · have hc : (X.g.L.flippable x).card ≤ X.g.L.m := by
            simpa using Finset.card_le_univ (X.g.L.flippable x)
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le hc))
      alarm (fun q => r ^ (q.2.1 + 1)) (fun q _ => (pow_pos hr0 _).le)
      (by
        intro x hx y hy hxy c hax
        obtain ⟨_, _, hxJ⟩ := (Finset.mem_filter.mp hx).2
        obtain ⟨_, _, hyJ⟩ := (Finset.mem_filter.mp hy).2
        have hk : X.g.L.key x = X.g.L.key y := congrArg Prod.fst hxy
        have hs : X.g.L.severity x = X.g.L.severity y := congrArg (fun q => q.2.1) hxy
        have hF : (X.g.L.flippable x).card = (X.g.L.flippable y).card := congrArg (fun q => q.2.2) hxy
        have hR : R x c = R y c := low_step2_rate_eq X x y hxJ hk hs hF (v, c)
        have hu : (X.evenType x).u = (X.evenType y).u := by
          rw [evenType_u_low X x hxJ, evenType_u_low X y hyJ, hs]
        show r ^ (X.evenType y).u < R y c
        rw [← hu, ← hR]
        exact hax)
      (by
        intro x hx
        obtain ⟨hxe, hxi, hxJ⟩ := (Finset.mem_filter.mp hx).2
        have h := hx_alarm x hxe hxi
        rw [evenType_u_low X x hxJ] at h
        exact h)
    refine hmain.trans ?_
    have hsum : ∑ q ∈ Ulow, r ^ (q.2.1 + 1) =
        ∑ _h ∈ keysAt X i, ((X.g.L.m : ℝ) + 1) * ∑ j ∈ Finset.range (X.J + 1), r ^ (j + 1) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.sum_product, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      show ∑ _y ∈ Finset.range (X.g.L.m + 1), r ^ (j + 1) = ((X.g.L.m : ℝ) + 1) * r ^ (j + 1)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    rw [hsum, Finset.sum_const, nsmul_eq_mul]
    have hgeo := sum_positive_powers_le r hr0.le (by simpa [hrdef] using hr) (X.J + 1)
    have hkeys : ((keysAt X i).card : ℝ) ≤ 2 := by exact_mod_cast keysAt_card_le X i
    have hm0 : (0 : ℝ) ≤ (X.g.L.m : ℝ) + 1 := by positivity
    have hinner : ((X.g.L.m : ℝ) + 1) * ∑ j ∈ Finset.range (X.J + 1), r ^ (j + 1) ≤
        ((X.g.L.m : ℝ) + 1) * (2 * r) := mul_le_mul_of_nonneg_left hgeo hm0
    have hinner0 : 0 ≤ ((X.g.L.m : ℝ) + 1) * ∑ j ∈ Finset.range (X.J + 1), r ^ (j + 1) :=
      mul_nonneg hm0 (Finset.sum_nonneg fun j _ => (pow_pos hr0 _).le)
    have hmm : ((X.m : ℝ) + 1) = (X.g.L.m : ℝ) + 1 := rfl
    rw [hmm]
    nlinarith
  -- high types
  let Shigh : Finset (CubeVertex n) := Finset.univ.filter fun x =>
    IsEvenRole x ∧ (X.g.L.key x).1 = i ∧ ¬ X.g.L.severity x ≤ X.J
  let Uhigh : Finset (X.Key × Bool) := keysAt X i ×ˢ (Finset.univ : Finset Bool)
  have hhigh : (X.coarseLaw v).pr (fun c => ∃ x ∈ Shigh, alarm x c) ≤ 4 * r := by
    have hmain := pr_exists_code_le (X.coarseLaw v) Shigh Uhigh
      (fun x => (X.g.L.key x, decide (X.g.L.severity x = X.J + 1)))
      (by
        intro x hx
        obtain ⟨_, hxi, _⟩ := (Finset.mem_filter.mp hx).2
        exact Finset.mem_product.mpr ⟨mem_keysAt X _ i hxi, Finset.mem_univ _⟩)
      alarm (fun _ => r) (fun _ _ => hr0.le)
      (by
        intro x hx y hy hxy c hax
        obtain ⟨_, _, hxJ⟩ := (Finset.mem_filter.mp hx).2
        obtain ⟨_, _, hyJ⟩ := (Finset.mem_filter.mp hy).2
        have hk : X.g.L.key x = X.g.L.key y := congrArg Prod.fst hxy
        have hopt : X.g.L.severity x = X.J + 1 ↔ X.g.L.severity y = X.J + 1 :=
          decide_eq_decide.mp (congrArg Prod.snd hxy)
        have hR : R x c = R y c := high_step2_rate_eq X x y hxJ hyJ hk hopt (v, c)
        have hu : (X.evenType x).u = (X.evenType y).u := by
          rw [evenType_u_high X x hxJ, evenType_u_high X y hyJ]
        show r ^ (X.evenType y).u < R y c
        rw [← hu, ← hR]
        exact hax)
      (by
        intro x hx
        obtain ⟨hxe, hxi, hxJ⟩ := (Finset.mem_filter.mp hx).2
        have h := hx_alarm x hxe hxi
        rw [evenType_u_high X x hxJ, pow_one] at h
        exact h)
    refine hmain.trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Uhigh.card : ℝ) ≤ 4 := by
      have h1 : Uhigh.card = (keysAt X i).card * 2 := by
        simp [Uhigh, Finset.card_product]
      have h2 := keysAt_card_le X i
      exact_mod_cast (show Uhigh.card ≤ 4 by omega)
    nlinarith
  -- combine
  have hsplit : ∀ c, (∃ x : CubeVertex n, IsEvenRole x ∧ (X.g.L.key x).1 = i ∧
      (n : ℝ) ^ (-(δ₂ * (X.evenType x).u / 8)) < R x c) →
        (∃ x ∈ Slow, alarm x c) ∨ ∃ x ∈ Shigh, alarm x c := by
    rintro c ⟨x, hxe, hxi, hax⟩
    have hax' := (halarm_eq x c).mp hax
    by_cases hxJ : X.g.L.severity x ≤ X.J
    · exact Or.inl ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxe, hxi, hxJ⟩, hax'⟩
    · exact Or.inr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxe, hxi, hxJ⟩, hax'⟩
  calc
    _ ≤ (X.coarseLaw v).pr (fun c => (∃ x ∈ Slow, alarm x c) ∨ ∃ x ∈ Shigh, alarm x c) :=
      Lane_q_s06_stages.pr_mono _ hsplit
    _ ≤ (X.coarseLaw v).pr (fun c => ∃ x ∈ Slow, alarm x c) +
        (X.coarseLaw v).pr (fun c => ∃ x ∈ Shigh, alarm x c) := FinProb.pr_union _ _ _
    _ ≤ 4 * ((X.m : ℝ) + 1) * r + 4 * r := add_le_add hlow hhigh
    _ ≤ 8 * ((X.m : ℝ) + 1) * r := by
      have hm0 : (0 : ℝ) ≤ X.m := Nat.cast_nonneg _
      nlinarith

/-! ### Step 3: transport of the raw rate under key-preserving hidden permutations -/

/-- Reindexing the tuple data by the type renaming. -/
def dataPerm (e : Equiv.Perm X.HKey) : Equiv.Perm (Fin X.T × X.Ty) :=
  Equiv.prodCongr (Equiv.refl (Fin X.T)) (typePermEquiv X e)

@[simp] theorem dataPerm_apply (e : Equiv.Perm X.HKey) (p : Fin X.T × X.Ty) :
    dataPerm X e p = (p.1, renamedType X e p.2) := rfl

theorem hiddenPermEquiv_update (e : Equiv.Perm X.HKey) (Z : X.Hid) (ℓ : X.HKey) (ξ : Fin N) :
    hiddenPermEquiv X e (Function.update Z ℓ ξ) = Function.update (hiddenPermEquiv X e Z) (e ℓ) ξ := by
  funext ℓ'
  rw [hiddenPermEquiv_apply]
  by_cases h : ℓ' = e ℓ
  · subst h
    rw [Equiv.symm_apply_apply, Function.update_self, Function.update_self]
  · have hne : e.symm ℓ' ≠ ℓ := fun h' => h (by rw [← h', Equiv.apply_symm_apply])
    rw [Function.update_of_ne h, Function.update_of_ne hne, hiddenPermEquiv_apply]

theorem tupleRatio_hiddenPerm (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1)
    (b₁ b₂ : X.Base) (Z₁ Z₂ : X.Hid) (β : X.Ty) (T₁ : FinProb X.ι) (drop : X.Name) (ob : X.Tuple) :
    X.tupleRatio (b₁, hiddenPermEquiv X e Z₁) (b₂, hiddenPermEquiv X e Z₂) (renamedType X e β) T₁
        (namePermEquiv X e drop) ob =
      X.tupleRatio (b₁, Z₁) (b₂, Z₂) β T₁ drop ob := by
  unfold Ctx6.tupleRatio
  rw [Tβ_hiddenPerm X b₁ e he β Z₁, reqNames_renamedType,
    ← Finset.image_erase (namePermEquiv X e).injective]
  simp only [labelLaw_hiddenPerm]

theorem locHid_image (e : Equiv.Perm X.HKey) (D : Finset (Fin X.T × X.Ty)) :
    X.locHid (D.image (dataPerm X e)) = (X.locHid D).image e := by
  unfold Ctx6.locHid
  rw [Finset.biUnion_image, Finset.image_biUnion]
  rfl

theorem locKeys_image (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (D : Finset (Fin X.T × X.Ty)) :
    X.locKeys (D.image (dataPerm X e)) = X.locKeys D := by
  unfold Ctx6.locKeys
  rw [locHid_image, Finset.image_biUnion, Finset.image_image]
  simp only [he]
  try rfl

theorem locDensity_hiddenPerm (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1) (base : X.Base)
    (Z : X.Hid) (nm : ParentName6 X.Bin) (D : Finset (Fin X.T × X.Ty)) (ξ : Fin N) :
    X.locDensity (base, hiddenPermEquiv X e Z) nm (D.image (dataPerm X e)) ξ =
      X.locDensity (base, Z) nm D ξ := by
  unfold Ctx6.locDensity Ctx6.locBins
  dsimp only
  rw [locKeys_image X e he, locHid_image, Finset.prod_image (fun x _ y _ h => e.injective h)]
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ _
  show (N : ℝ) * (X.hidPost (X.withPar base nm ξ) (e ℓ).1).w (Z (e.symm (e ℓ))) =
    (N : ℝ) * (X.hidPost (X.withPar base nm ξ) ℓ.1).w (Z ℓ)
  rw [he, Equiv.symm_apply_apply]

section S3Transport

variable (base : X.Base) (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1)
  (a a' : X.State) (hkey : X.g.L.stKey a' = X.g.L.stKey a) (hmode : X.stMode a' = X.stMode a)
  (htgt : X.tgt a' = e (X.tgt a)) (D : Finset (Fin X.T × X.Ty)) (Z : X.Hid) (o : X.Data (Fin X.T))

include he htgt in
theorem withHid_hiddenPerm (ξ : Fin N) :
    X.withHid (base, hiddenPermEquiv X e Z) (X.tgt a') ξ =
      (base, hiddenPermEquiv X e (Function.update Z (X.tgt a) ξ)) := by
  show (base, Function.update (hiddenPermEquiv X e Z) (X.tgt a') ξ) = _
  rw [htgt, hiddenPermEquiv_update]

include he htgt in
theorem lowGate_hiddenPerm (ξ : Fin N) :
    X.LowGate (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e)) ξ ↔ X.LowGate (base, Z) a D ξ := by
  have hk : (X.tgt a').1 = (X.tgt a).1 := by rw [htgt, he]
  unfold Ctx6.LowGate
  rw [withHid_hiddenPerm X base e he a a' htgt Z ξ, hk]
  apply and_congr Iff.rfl (and_congr Iff.rfl ?_)
  rw [Finset.forall_mem_image]
  exact forall₂_congr fun p _ => step2Tests_hiddenPerm X base e he p.2 _

include he htgt in
theorem lowLik_hiddenPerm (ξ : Fin N) (β : X.Ty) (ob : X.Tuple) :
    X.lowLik (base, hiddenPermEquiv X e Z) a' ξ (renamedType X e β) ob = X.lowLik (base, Z) a ξ β ob := by
  unfold Ctx6.lowLik
  rw [withHid_hiddenPerm X base e he a a' htgt Z ξ, htgt, TβDel_hiddenPerm X base e he β Z]
  exact tupleRatio_hiddenPerm X e he base base _ Z β _ (.hid (X.tgt a)) ob

theorem dropMap_eq_some (σ : Equiv.Perm (Fin X.T × X.Ty)) (drop : Option (Fin X.T × X.Ty))
    (p : Fin X.T × X.Ty) : drop.map σ = some (σ p) ↔ drop = some p := by
  cases drop with
  | none => simp
  | some q => simp [σ.injective.eq_iff]

include he htgt in
theorem lowWeight_hiddenPerm (drop : Option (Fin X.T × X.Ty)) (ξ : Fin N) :
    X.lowWeight (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
        (fun p => o ((dataPerm X e).symm p)) (drop.map (dataPerm X e)) ξ =
      X.lowWeight (base, Z) a D o drop ξ := by
  have hk : (X.tgt a').1 = (X.tgt a).1 := by rw [htgt, he]
  unfold Ctx6.lowWeight
  have hgate := propext (lowGate_hiddenPerm X base e he a a' htgt D Z ξ)
  rw [hk, Finset.prod_image (fun x _ y _ h => (dataPerm X e).injective h)]
  simp only [hgate]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  show (if drop.map (dataPerm X e) = some (dataPerm X e p) then (1 : ℝ) else
      X.lowLik (base, hiddenPermEquiv X e Z) a' ξ (renamedType X e p.2)
        (o ((dataPerm X e).symm (dataPerm X e p)))) =
    (if drop = some p then (1 : ℝ) else X.lowLik (base, Z) a ξ p.2 (o p))
  by_cases hp : drop = some p
  · rw [if_pos ((dropMap_eq_some X _ drop p).mpr hp), if_pos hp]
  · rw [if_neg (fun h => hp ((dropMap_eq_some X _ drop p).mp h)), if_neg hp, Equiv.symm_apply_apply,
      lowLik_hiddenPerm X base e he a a' htgt Z ξ p.2 (o p)]

include hkey in
theorem tgtName_eq : X.tgtName a' = X.tgtName a := by
  unfold Ctx6.tgtName
  rw [hkey]

include he hkey in
theorem highGate_hiddenPerm (ξ : Fin N) :
    X.HighGate (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e)) ξ ↔
      X.HighGate (base, Z) a D ξ := by
  unfold Ctx6.HighGate
  rw [tgtName_eq X a a' hkey, locHid_image]
  apply and_congr Iff.rfl (and_congr ?_ ?_)
  · rw [Finset.forall_mem_image]
    exact forall₂_congr fun ℓ _ => by rw [he] <;> exact Iff.rfl
  · rw [Finset.forall_mem_image]
    exact forall₂_congr fun p _ => step2Tests_hiddenPerm X (X.withPar base (X.tgtName a) ξ) e he p.2 Z

include he hkey in
theorem highLik_hiddenPerm (ξ : Fin N) (β : X.Ty) (ob : X.Tuple) :
    X.highLik (base, hiddenPermEquiv X e Z) a' ξ (renamedType X e β) ob = X.highLik (base, Z) a ξ β ob := by
  unfold Ctx6.highLik
  rw [tgtName_eq X a a' hkey]
  exact tupleRatio_hiddenPerm X e he (X.withPar base (X.tgtName a) ξ) base Z Z β _ (.par (X.tgtName a)) ob

include he hkey in
theorem highWeight_hiddenPerm (drop : Option (Fin X.T × X.Ty)) (ξ : Fin N) :
    X.highWeight (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
        (fun p => o ((dataPerm X e).symm p)) (drop.map (dataPerm X e)) ξ =
      X.highWeight (base, Z) a D o drop ξ := by
  have hgate := propext (highGate_hiddenPerm X base e he a a' hkey D Z ξ)
  unfold Ctx6.highWeight
  simp only [hgate]
  rw [tgtName_eq X a a' hkey, locDensity_hiddenPerm X e he base Z _ D ξ,
    Finset.prod_image (fun x _ y _ h => (dataPerm X e).injective h)]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  show (if drop.map (dataPerm X e) = some (dataPerm X e p) then (1 : ℝ) else
      X.highLik (base, hiddenPermEquiv X e Z) a' ξ (renamedType X e p.2)
        (o ((dataPerm X e).symm (dataPerm X e p)))) =
    (if drop = some p then (1 : ℝ) else X.highLik (base, Z) a ξ p.2 (o p))
  by_cases hp : drop = some p
  · rw [if_pos ((dropMap_eq_some X _ drop p).mpr hp), if_pos hp]
  · rw [if_neg (fun h => hp ((dropMap_eq_some X _ drop p).mp h)), if_neg hp, Equiv.symm_apply_apply,
      highLik_hiddenPerm X base e he a a' hkey Z ξ p.2 (o p)]

include he hkey hmode htgt in
theorem s3Mass_hiddenPerm (drop : Option (Fin X.T × X.Ty)) :
    X.s3Mass (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
        (fun p => o ((dataPerm X e).symm p)) (drop.map (dataPerm X e)) =
      X.s3Mass (base, Z) a D o drop := by
  unfold Ctx6.s3Mass Ctx6.s3Weight
  rw [hmode]
  apply Finset.sum_congr rfl
  intro ξ _
  cases X.stMode a with
  | low => exact lowWeight_hiddenPerm X base e he a a' htgt D Z o drop ξ
  | high => exact highWeight_hiddenPerm X base e he a a' hkey D Z o drop ξ

include he hkey hmode htgt in
theorem s3TrueGate_hiddenPerm :
    X.S3TrueGate (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e)) ↔
      X.S3TrueGate (base, Z) a D := by
  unfold Ctx6.S3TrueGate Ctx6.trueTarget
  rw [hmode]
  cases X.stMode a with
  | low =>
    show X.LowGate (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
        (hiddenPermEquiv X e Z (X.tgt a')) ↔ X.LowGate (base, Z) a D (Z (X.tgt a))
    rw [htgt, hiddenPermEquiv_apply, Equiv.symm_apply_apply]
    exact lowGate_hiddenPerm X base e he a a' htgt D Z _
  | high =>
    show X.HighGate (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
        ((X.parOf base).val (X.tgtName a')) ↔ X.HighGate (base, Z) a D ((X.parOf base).val (X.tgtName a))
    rw [tgtName_eq X a a' hkey]
    exact highGate_hiddenPerm X base e he a a' hkey D Z _

end S3Transport

/-- (B1a, 06:303–447).  The Step 3 failure event is equivariant under a key-preserving permutation `e` of
hidden keys: renaming the hidden scalars, the observation lists of the descriptor's types, the target key and the
data indices together preserves the low and high integrands, gates, masses and tests. -/
theorem s3Fail_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1)
    (a a' : X.State) (hkey : X.g.L.stKey a' = X.g.L.stKey a) (hmode : X.stMode a' = X.stMode a)
    (htgt : X.tgt a' = e (X.tgt a)) (D : Finset (Fin X.T × X.Ty)) (Z : X.Hid)
    (o : X.Data (Fin X.T)) :
    X.S3Fail (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
        (fun p => o ((dataPerm X e).symm p)) ↔ X.S3Fail (base, Z) a D o := by
  have hmass := s3Mass_hiddenPerm X base e he a a' hkey hmode htgt D Z o
  have hnone : X.s3Mass (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
      (fun p => o ((dataPerm X e).symm p)) none = X.s3Mass (base, Z) a D o none := hmass none
  have hmatch : ∀ β : X.Ty, X.Matching a' (renamedType X e β) ↔ X.Matching a β := by
    intro β
    unfold Ctx6.Matching
    rw [renamedType_mode, renamedType_key, hmode, hkey]
  unfold Ctx6.S3Fail Ctx6.S3Tests
  rw [s3TrueGate_hiddenPerm X base e he a a' hkey hmode htgt D Z, hnone]
  apply and_congr Iff.rfl (not_congr (and_congr Iff.rfl (and_congr Iff.rfl ?_)))
  rw [Finset.forall_mem_image]
  refine forall₂_congr fun p _ => ?_
  have hs : X.s3Mass (base, hiddenPermEquiv X e Z) a' (D.image (dataPerm X e))
      (fun p => o ((dataPerm X e).symm p)) (some (dataPerm X e p)) =
        X.s3Mass (base, Z) a D o (some p) := hmass (some p)
  simp only [hs]
  exact imp_congr (hmatch p.2) Iff.rfl


/-- (B1b, 06:141–144).  The tuple data law at renamed hidden scalars is the reindexed data law. -/
theorem dataLaw_pr_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1)
    (Z : X.Hid) (P : X.Data (Fin X.T) → Prop) :
    (X.dataLaw (Fin X.T) (base, hiddenPermEquiv X e Z)).pr P =
      (X.dataLaw (Fin X.T) (base, Z)).pr (fun o => P (fun p => o ((dataPerm X e).symm p))) := by
  have htype : ∀ β : X.Ty, X.tupleLaw (base, Z) (renamedType X e.symm β) =
      X.tupleLaw (base, hiddenPermEquiv X e Z) β := by
    intro β
    have hinv : renamedType X e (renamedType X e.symm β) = β := by
      have h := renamedType_inverse X e.symm β
      rwa [Equiv.symm_symm] at h
    have h := tupleLaw_hiddenPerm X base e he (renamedType X e.symm β) Z
    rw [hinv] at h
    exact h.symm
  have hw : ∀ o : X.Data (Fin X.T), (X.dataLaw (Fin X.T) (base, Z)).w (fun p => o (dataPerm X e p)) =
      (X.dataLaw (Fin X.T) (base, hiddenPermEquiv X e Z)).w o := by
    intro o
    show (∏ p, (X.tupleLaw (base, Z) p.2).w (o (dataPerm X e p))) =
      ∏ p, (X.tupleLaw (base, hiddenPermEquiv X e Z) p.2).w (o p)
    rw [← Equiv.prod_comp (dataPerm X e).symm]
    apply Finset.prod_congr rfl
    intro p _
    simp only [Equiv.apply_symm_apply]
    show (X.tupleLaw (base, Z) (renamedType X e.symm p.2)).w (o p) = _
    rw [htype]
  let Φ : X.Data (Fin X.T) ≃ X.Data (Fin X.T) := Equiv.arrowCongr (dataPerm X e) (Equiv.refl X.Tuple)
  unfold FinProb.pr
  rw [← Equiv.sum_comp Φ.symm (fun o => if P (fun p => o ((dataPerm X e).symm p)) then
    (X.dataLaw (Fin X.T) (base, Z)).w o else 0)]
  apply Finset.sum_congr rfl
  intro o _
  have hPo : (fun p => (Φ.symm o) ((dataPerm X e).symm p)) = o := by
    funext p
    show o (dataPerm X e ((dataPerm X e).symm p)) = o p
    rw [Equiv.apply_symm_apply]
  have hwo : (X.dataLaw (Fin X.T) (base, Z)).w (Φ.symm o) =
      (X.dataLaw (Fin X.T) (base, hiddenPermEquiv X e Z)).w o := hw o
  have hPo' : P (fun p => (Φ.symm o) ((dataPerm X e).symm p)) ↔ P o := by rw [hPo]
  by_cases hP : P o
  · rw [if_pos hP, if_pos (hPo'.mpr hP), hwo]
  · rw [if_neg hP, if_neg (fun h => hP (hPo'.mp h))]


/-- The base-level Step 3 rate is invariant under key-preserving hidden permutations (B1). -/
theorem rate3Base_hiddenPerm (base : X.Base) (e : Equiv.Perm X.HKey) (he : ∀ ℓ, (e ℓ).1 = ℓ.1)
    (a a' : X.State) (hkey : X.g.L.stKey a' = X.g.L.stKey a) (hmode : X.stMode a' = X.stMode a)
    (htgt : X.tgt a' = e (X.tgt a)) (D : Finset (Fin X.T × X.Ty)) :
    (X.hidLaw base).expect (fun Z => (X.dataLaw (Fin X.T) (base, Z)).pr
        (fun o => X.S3Fail (base, Z) a' (D.image (dataPerm X e)) o)) =
      (X.hidLaw base).expect (fun Z => (X.dataLaw (Fin X.T) (base, Z)).pr
        (fun o => X.S3Fail (base, Z) a D o)) := by
  rw [hidLaw_expect_hiddenPerm X base e he]
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only
  congr 1
  rw [dataLaw_pr_hiddenPerm X base e he Z]
  exact Lane_q_s06_stages.pr_congr _ fun o => s3Fail_hiddenPerm X base e he a a' hkey hmode htgt D Z o

/-! ### Step 3: sign translation and descriptor shapes at a bin -/

def signXor {m : ℕ} (t s : CubeVertex m) : CubeVertex m := fun j => xor (t j) (s j)

private theorem xor_xor_cancel (a b : Bool) : xor (xor a b) b = a := by cases a <;> cases b <;> rfl

private theorem xor_xor_three (a b c : Bool) : xor (xor a (xor b c)) c = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem xor_cancel_left (a b : Bool) : xor a (xor a b) = b := by cases a <;> cases b <;> rfl

/-- Central-sign translation of hidden keys. -/
def signShift (s : CubeVertex X.g.L.m) : Equiv.Perm X.HKey where
  toFun ℓ := (ℓ.1, signXor ℓ.2 s)
  invFun ℓ := (ℓ.1, signXor ℓ.2 s)
  left_inv ℓ := Prod.ext rfl (funext fun j => xor_xor_cancel _ _)
  right_inv ℓ := Prod.ext rfl (funext fun j => xor_xor_cancel _ _)

theorem signShift_fst (s : CubeVertex X.g.L.m) (ℓ : X.HKey) : (signShift X s ℓ).1 = ℓ.1 := rfl

/-- A descriptor translated by a central sign. -/
def descShift (s : CubeVertex X.g.L.m) (D : Finset (Fin X.T × X.Ty)) : Finset (Fin X.T × X.Ty) :=
  D.image (dataPerm X (signShift X s))

theorem descShift_injective (s : CubeVertex X.g.L.m) : Function.Injective (descShift X s) :=
  Finset.image_injective (dataPerm X (signShift X s)).injective

theorem renamedType_comp (e e' : Equiv.Perm X.HKey) (β : X.Ty) :
    renamedType X e (renamedType X e' β) = renamedType X (e'.trans e) β := by
  rcases β with ⟨h, mode, j, obs⟩
  change (h, mode, j, (obs.image e').image e) = (h, mode, j, obs.image (e'.trans e))
  rw [Finset.image_image]
  rfl

theorem signShift_trans (t t' : CubeVertex X.g.L.m) :
    (signShift X (signXor t t')).trans (signShift X t') = signShift X t := by
  apply Equiv.ext
  intro ℓ
  exact Prod.ext rfl (funext fun j => xor_xor_three _ _ _)

/-- The central sign `0`. -/
def zeroSign : CubeVertex X.m := fun _ => false

/-- The coarse shape of a descriptor at an odd state: flag, mode, and the descriptor translated to sign `0`. -/
def coarseShape (a : X.State) (D : Finset (Fin X.T × X.Ty)) : DescriptorShape X :=
  ((X.g.L.stKey a).2, X.stMode a, descShift X (X.g.L.stSign a) D)

/-- Far-high descriptor shapes: every observed type is high with an empty list. -/
def farShapeCodes (i : X.Bin) : Finset (DescriptorShape X) :=
  (Finset.univ : Finset KeyFlag6).biUnion fun f =>
    (((Finset.univ : Finset (Fin X.T)) ×ˢ
        ((X.C (i, f)).image fun k => ((k, Mode6.high, 0, ∅) : X.Ty))).powerset).image
      fun D => (f, Mode6.high, D)

def coarseShapeCodes (i : X.Bin) : Finset (DescriptorShape X) :=
  groupDescriptorShapeCodes X (i, zeroSign X) ∪ farShapeCodes X i

theorem flip_signXor {m : ℕ} (t s : CubeVertex m) (a : Fin m) :
    signXor (flipVertex6 t a) s = flipVertex6 (signXor t s) a := by
  funext j
  by_cases hja : j = a
  · subst hja
    show xor (Function.update t j (!t j) j) (s j) = Function.update (signXor t s) j (!(signXor t s j)) j
    rw [Function.update_self, Function.update_self]
    show xor (!t j) (s j) = !(xor (t j) (s j))
    cases t j <;> cases s j <;> rfl
  · show xor (Function.update t a (!t a) j) (s j) = Function.update (signXor t s) a (!(signXor t s a)) j
    rw [Function.update_of_ne hja, Function.update_of_ne hja]
    rfl

theorem signXor_self {m : ℕ} (t : CubeVertex m) : signXor t t = fun _ => false := by
  funext j
  show xor (t j) (t j) = false
  cases t j <;> rfl

theorem lowObservations_shift (s : CubeVertex X.m) (k : X.Key) (t : CubeVertex X.m)
    (F : Finset (Fin X.m)) :
    (lowObservations6 binAdjacent6 k t F).image (signShift X s) =
      lowObservations6 binAdjacent6 k (signXor t s) F := by
  ext ℓ
  constructor
  · intro hℓ
    rcases Finset.mem_image.mp hℓ with ⟨ℓ₀, hℓ₀, rfl⟩
    rcases (mem_lowObservations_iff binAdjacent6 k t F ℓ₀).mp hℓ₀ with ⟨k', hk', rfl⟩ | ⟨a, ha, rfl⟩
    · exact (mem_lowObservations_iff binAdjacent6 k (signXor t s) F _).mpr (Or.inl ⟨k', hk', rfl⟩)
    · exact (mem_lowObservations_iff binAdjacent6 k (signXor t s) F _).mpr
        (Or.inr ⟨a, ha, Prod.ext rfl (flip_signXor t s a).symm⟩)
  · intro hℓ
    rcases (mem_lowObservations_iff binAdjacent6 k (signXor t s) F ℓ).mp hℓ with
      ⟨k', hk', rfl⟩ | ⟨a, ha, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k', t),
        (mem_lowObservations_iff binAdjacent6 k t F _).mpr (Or.inl ⟨k', hk', rfl⟩), rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, flipVertex6 t a),
        (mem_lowObservations_iff binAdjacent6 k t F _).mpr (Or.inr ⟨a, ha, rfl⟩),
        Prod.ext rfl (flip_signXor t s a)⟩

theorem image_singleton_eq {α β : Type*} [DecidableEq β] (f : α → β) (a : α) (b : β) (h : f a = b) :
    ({a} : Finset α).image f = {b} := by
  rw [Finset.image_singleton, h]

theorem makeType_shift (s : CubeVertex X.m) (k : X.Key) (t : CubeVertex X.m)
    (F : Finset (Fin X.m)) (j : ℕ) :
    renamedType X (signShift X s) (makeType6 binAdjacent6 k t F j X.J) =
      makeType6 binAdjacent6 k (signXor t s) F j X.J := by
  by_cases hj : j ≤ X.J
  · simp only [makeType6, if_pos hj]
    show (k, Mode6.low, sevFin6 X.m j,
      (lowObservations6 binAdjacent6 k t F).image (signShift X s)) = _
    rw [lowObservations_shift]
    rfl
  · simp only [makeType6, if_neg hj]
    show (k, Mode6.high, (0 : Fin (X.m + 1)),
      (highObservations6 k t j X.J).image (signShift X s)) = _
    unfold highObservations6
    by_cases hJ : j = X.J + 1
    · rw [if_pos hJ, if_pos hJ]
      exact congrArg (Prod.mk k) (congrArg (Prod.mk Mode6.high) (congrArg (Prod.mk 0)
        (image_singleton_eq _ _ _ rfl)))
    · rw [if_neg hJ, if_neg hJ]
      exact congrArg (Prod.mk k) (congrArg (Prod.mk Mode6.high) (congrArg (Prod.mk 0)
        (Finset.image_empty _)))

theorem universe_shift (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ)
    (β : X.Ty) (hβ : β ∈ neighborTypeUniverse X h t F j) :
    renamedType X (signShift X t) β ∈ neighborTypeUniverse X h (zeroSign X) F j := by
  unfold neighborTypeUniverse at hβ ⊢
  rcases Finset.mem_biUnion.mp hβ with ⟨k, hk, hβ⟩
  rcases Finset.mem_biUnion.mp hβ with ⟨s', hs', hβ⟩
  rcases Finset.mem_biUnion.mp hβ with ⟨F', hF', hβ⟩
  rcases Finset.mem_image.mp hβ with ⟨j', hj', rfl⟩
  rw [makeType_shift]
  refine Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_biUnion.mpr ⟨signXor s' t, ?_,
    Finset.mem_biUnion.mpr ⟨F', hF', Finset.mem_image.mpr ⟨j', hj', rfl⟩⟩⟩⟩
  unfold closedSignNeighbors at hs' ⊢
  rcases Finset.mem_insert.mp hs' with hs' | hs'
  · rw [hs', signXor_self]
    exact Finset.mem_insert_self _ _
  · rcases Finset.mem_image.mp hs' with ⟨a, _, rfl⟩
    apply Finset.mem_insert_of_mem
    refine Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩
    rw [flip_signXor, signXor_self]
    rfl

theorem generic_shift (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ)
    (β : X.Ty) (hβ : β ∈ genericNeighborTypes X h t F j) :
    renamedType X (signShift X t) β ∈ genericNeighborTypes X h (zeroSign X) F j := by
  unfold genericNeighborTypes at hβ ⊢
  rcases Finset.mem_biUnion.mp hβ with ⟨k, hk, hβ⟩
  rcases Finset.mem_image.mp hβ with ⟨j', hj', rfl⟩
  rw [makeType_shift, signXor_self]
  exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_image.mpr ⟨j', hj', rfl⟩⟩

theorem descriptorCodes_shift (h : X.Key) (t : CubeVertex X.m) (F : Finset (Fin X.m)) (j : ℕ)
    (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ descriptorCodes X h t F j) :
    descShift X t D ∈ descriptorCodes X h (zeroSign X) F j := by
  unfold descriptorCodes at hD ⊢
  rcases Finset.mem_image.mp hD with ⟨q, hq, rfl⟩
  rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
  rcases Finset.mem_biUnion.mp hq2 with ⟨r, hr, hq2⟩
  rcases Finset.mem_powersetCard.mp hq2 with ⟨hsub2, hcard2⟩
  refine Finset.mem_image.mpr ⟨(descShift X t q.1, descShift X t q.2),
    Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · apply Finset.mem_powerset.mpr
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p₀, hp₀, rfl⟩
    have hp₁ := Finset.mem_product.mp (Finset.mem_powerset.mp hq1 hp₀)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, generic_shift X h t F j _ hp₁.2⟩
  · refine Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro p hp
      rcases Finset.mem_image.mp hp with ⟨p₀, hp₀, rfl⟩
      have hp₁ := Finset.mem_product.mp (hsub2 hp₀)
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, universe_shift X h t F j _ hp₁.2⟩
    · unfold descShift
      rw [Finset.card_image_of_injective _ (dataPerm X (signShift X t)).injective, hcard2]
  · show descShift X t q.1 ∪ descShift X t q.2 = descShift X t (q.1 ∪ q.2)
    unfold descShift
    rw [Finset.image_union]

/-- (B2, 06:282–292).  Near states: translating the descriptor to sign `0` lands in Sol's code set at
sign `0` (generic and neighbouring type universes are translation-equivariant). -/
theorem near_coarseShape_mem (hn : 4 ≤ n) (a : X.State) (ha : a ∈ X.g.L.oddStates)
    (hj : X.g.L.stSeverity a ≤ X.J + 2) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs a) :
    coarseShape X a D ∈ groupDescriptorShapeCodes X ((X.g.L.stKey a).1, zeroSign X) := by
  have hF : (X.g.L.stFlippable a).card ≤ X.J + 2 := (state_flippable_card_le_severity X a ha).trans hj
  have hc := descriptorCodes_shift X _ _ _ _ D (descriptor_mem_codes X a ha hn D hD)
  unfold groupDescriptorShapeCodes coarseShape
  refine Finset.mem_biUnion.mpr ⟨((X.g.L.stKey a).2, X.stMode a),
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
    Finset.mem_biUnion.mpr ⟨X.g.L.stSeverity a, Finset.mem_range.mpr (by omega),
      Finset.mem_biUnion.mpr ⟨X.g.L.stFlippable a, ?_, Finset.mem_image.mpr ⟨_, hc, rfl⟩⟩⟩⟩
  exact Finset.mem_biUnion.mpr ⟨(X.g.L.stFlippable a).card, Finset.mem_range.mpr (by omega),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩


theorem far_type_eq (a : X.State) (hj : ¬ X.g.L.stSeverity a ≤ X.J + 2) (β : X.Ty)
    (hβ : β ∈ neighborTypeUniverse X (X.g.L.stKey a) (X.g.L.stSign a) (X.g.L.stFlippable a)
      (X.g.L.stSeverity a)) :
    ∃ k ∈ X.C (X.g.L.stKey a), β = (k, Mode6.high, 0, ∅) := by
  unfold neighborTypeUniverse at hβ
  rcases Finset.mem_biUnion.mp hβ with ⟨k, hk, hβ⟩
  rcases Finset.mem_biUnion.mp hβ with ⟨s, _, hβ⟩
  rcases Finset.mem_biUnion.mp hβ with ⟨F', _, hβ⟩
  rcases Finset.mem_image.mp hβ with ⟨j', hj', rfl⟩
  have hj'' : X.J + 2 ≤ j' := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    omega
  refine ⟨k, hk, ?_⟩
  have hlow : ¬ j' ≤ X.J := by omega
  have hne : j' ≠ X.J + 1 := by omega
  simp only [makeType6, if_neg hlow, highObservations6, if_neg hne]

theorem far_coarseShape_mem (a : X.State) (ha : a ∈ X.g.L.oddStates)
    (hj : ¬ X.g.L.stSeverity a ≤ X.J + 2) (D : Finset (Fin X.T × X.Ty)) (hD : D ∈ X.absDescs a) :
    coarseShape X a D ∈ farShapeCodes X (X.g.L.stKey a).1 := by
  have hmode : X.stMode a = Mode6.high := by
    unfold Ctx6.stMode modeOf6
    rw [if_neg (by omega)]
  have hsub : descShift X (X.g.L.stSign a) D ⊆ (Finset.univ : Finset (Fin X.T)) ×ˢ
      ((X.C ((X.g.L.stKey a).1, (X.g.L.stKey a).2)).image fun k => ((k, Mode6.high, 0, ∅) : X.Ty)) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p₀, hp₀, rfl⟩
    have hu := descriptor_subset_universe X a D hD hp₀
    have hβ := (Finset.mem_product.mp hu).2
    obtain ⟨k, hk, hkeq⟩ := far_type_eq X a hj p₀.2 hβ
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨k, hk, ?_⟩⟩
    show ((k, Mode6.high, 0, ∅) : X.Ty) = renamedType X (signShift X (X.g.L.stSign a)) p₀.2
    rw [hkeq]
    simp [renamedType, Type6.key, Type6.mode, Type6.obs]
  unfold farShapeCodes coarseShape
  rw [hmode]
  exact Finset.mem_biUnion.mpr ⟨(X.g.L.stKey a).2, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨_, Finset.mem_powerset.mpr hsub, rfl⟩⟩

theorem farShapeCodes_card_le (i : X.Bin) : (farShapeCodes X i).card ≤ 2 * 2 ^ (602 * X.T) := by
  have hflag : Fintype.card KeyFlag6 = 2 := by decide
  have hf : ∀ f ∈ (Finset.univ : Finset KeyFlag6),
      ((((Finset.univ : Finset (Fin X.T)) ×ˢ
        ((X.C (i, f)).image fun k => ((k, Mode6.high, 0, ∅) : X.Ty))).powerset).image
          fun D => (f, Mode6.high, D)).card ≤ 2 ^ (602 * X.T) := by
    intro f _
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_powerset]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have h1 := Finset.card_image_le (s := X.C (i, f)) (f := fun k => ((k, Mode6.high, 0, ∅) : X.Ty))
    have h2 : (X.C (i, f)).card ≤ 602 := X.g.flips.key_neighborhood_card (i, f)
    calc
      X.T * _ ≤ X.T * 602 := Nat.mul_le_mul_left _ (h1.trans h2)
      _ = 602 * X.T := Nat.mul_comm _ _
  have h := card_biUnion_le_uniform (Finset.univ : Finset KeyFlag6) _ _ hf
  rw [Finset.card_univ, hflag] at h
  exact h



theorem far_count_le_bound : 2 ^ (602 * X.T) ≤ descriptorCodeCountBound X := by
  unfold descriptorCodeCountBound
  have h1 : 2 ^ (602 * X.T) ≤ 2 ^ (1806 * X.T) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 0 < (X.T * 4000 * (X.m + 1) ^ 2 + 2) ^ (2 * (1 + 21 * (X.J + 2))) := pow_pos (by omega) _
  have h3 : 0 < 4 * (X.J + 3) * (X.m + 2) ^ (2 * (X.J + 2)) :=
    Nat.mul_pos (by omega) (pow_pos (by omega) _)
  calc
    2 ^ (602 * X.T) ≤ 2 ^ (1806 * X.T) * (X.T * 4000 * (X.m + 1) ^ 2 + 2) ^ (2 * (1 + 21 * (X.J + 2))) :=
      h1.trans (Nat.le_mul_of_pos_right _ h2)
    _ ≤ _ := Nat.le_mul_of_pos_left _ h3

theorem coarseShapeCodes_card_le (i : X.Bin) :
    (coarseShapeCodes X i).card ≤ 3 * descriptorCodeCountBound X := by
  have h1 := groupDescriptorShapeCodes_card_le X (i, zeroSign X)
  have h2 := farShapeCodes_card_le X i
  have h3 := far_count_le_bound X
  calc
    (coarseShapeCodes X i).card ≤ (groupDescriptorShapeCodes X (i, zeroSign X)).card +
        (farShapeCodes X i).card := Finset.card_union_le _ _
    _ ≤ 3 * descriptorCodeCountBound X := by omega

/-- Equal coarse shapes at one bin give equal base-level Step 3 rates at every base. -/
theorem coarseShape_rate_eq (base : X.Base) (a a' : X.State)
    (hbin : (X.g.L.stKey a).1 = (X.g.L.stKey a').1) (D D' : Finset (Fin X.T × X.Ty))
    (hshape : coarseShape X a D = coarseShape X a' D') :
    (X.hidLaw base).expect (fun Z => (X.dataLaw (Fin X.T) (base, Z)).pr
        (fun o => X.S3Fail (base, Z) a D o)) =
      (X.hidLaw base).expect (fun Z => (X.dataLaw (Fin X.T) (base, Z)).pr
        (fun o => X.S3Fail (base, Z) a' D' o)) := by
  have hflag : (X.g.L.stKey a).2 = (X.g.L.stKey a').2 := congrArg (fun s : DescriptorShape X => s.1) hshape
  have hmode : X.stMode a = X.stMode a' := congrArg (fun s : DescriptorShape X => s.2.1) hshape
  have hdesc : descShift X (X.g.L.stSign a) D = descShift X (X.g.L.stSign a') D' :=
    congrArg (fun s : DescriptorShape X => s.2.2) hshape
  have hkey : X.g.L.stKey a' = X.g.L.stKey a := Prod.ext hbin.symm hflag.symm
  set t := X.g.L.stSign a with ht
  set t' := X.g.L.stSign a' with ht'
  let e := signShift X (signXor t t')
  have hD' : D' = D.image (dataPerm X e) := by
    apply descShift_injective X t'
    rw [← hdesc]
    show D.image (dataPerm X (signShift X t)) =
      (D.image (dataPerm X e)).image (dataPerm X (signShift X t'))
    rw [Finset.image_image]
    apply Finset.image_congr
    intro p _
    show (p.1, renamedType X (signShift X t) p.2) = (p.1, renamedType X (signShift X t') (renamedType X e p.2))
    rw [renamedType_comp, signShift_trans]
  have htgt : X.tgt a' = e (X.tgt a) := by
    show (X.g.L.stKey a', t') = ((X.g.L.stKey a, t).1, signXor (X.g.L.stKey a, t).2 (signXor t t'))
    rw [hkey]
    exact Prod.ext rfl (funext fun j => (xor_cancel_left _ _).symm)
  rw [hD']
  exact (rate3Base_hiddenPerm X base e (fun _ => rfl) a a' hkey hmode.symm htgt D).symm

/-- The grouped future Step 3 alarms at a bin (06:488–496): Markov per descriptor and the union over coarse
shapes. -/
theorem coarse_step3_alarm_probability (v : Fin N) (i : X.Bin) (hn : 4 ≤ n) (s q : ℝ)
    (hs : 0 < s) (hq : 0 ≤ q)
    (hmean : ∀ a ∈ X.g.L.oddStates, ∀ D ∈ X.absDescs a,
      (X.coarseLaw v).expect (fun c => (X.hidLaw (v, c)).expect fun Z =>
        (X.dataLaw (Fin X.T) ((v, c), Z)).pr fun o => X.S3Fail ((v, c), Z) a D o) ≤ q) :
    (X.coarseLaw v).pr (fun c => ∃ a ∈ X.g.L.oddStates, (X.g.L.stKey a).1 = i ∧
        ∃ D ∈ X.absDescs a, s < (X.hidLaw (v, c)).expect fun Z =>
          (X.dataLaw (Fin X.T) ((v, c), Z)).pr fun o => X.S3Fail ((v, c), Z) a D o) ≤
      3 * (descriptorCodeCountBound X : ℝ) * (q / s) := by
  let R : X.State × Finset (Fin X.T × X.Ty) → X.Coarse → ℝ := fun p c =>
    (X.hidLaw (v, c)).expect fun Z =>
      (X.dataLaw (Fin X.T) ((v, c), Z)).pr fun o => X.S3Fail ((v, c), Z) p.1 p.2 o
  let S : Finset (X.State × Finset (Fin X.T × X.Ty)) :=
    (X.g.L.oddStates.filter fun a => (X.g.L.stKey a).1 = i).biUnion fun a =>
      (X.absDescs a).image fun D => (a, D)
  have hmemS : ∀ p ∈ S, p.1 ∈ X.g.L.oddStates ∧ (X.g.L.stKey p.1).1 = i ∧ p.2 ∈ X.absDescs p.1 := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨a, ha, hp⟩
    rcases Finset.mem_image.mp hp with ⟨D, hD, rfl⟩
    exact ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2, hD⟩
  have hsub : ∀ c, (∃ a ∈ X.g.L.oddStates, (X.g.L.stKey a).1 = i ∧
      ∃ D ∈ X.absDescs a, s < R (a, D) c) → ∃ p ∈ S, s < R p c := by
    rintro c ⟨a, ha, hai, D, hD, hr⟩
    exact ⟨(a, D), Finset.mem_biUnion.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hai⟩,
      Finset.mem_image.mpr ⟨D, hD, rfl⟩⟩, hr⟩
  have hU : ∀ p ∈ S, coarseShape X p.1 p.2 ∈ coarseShapeCodes X i := by
    intro p hp
    obtain ⟨ha, hai, hD⟩ := hmemS p hp
    by_cases hj : X.g.L.stSeverity p.1 ≤ X.J + 2
    · apply Finset.mem_union_left
      have h := near_coarseShape_mem X hn p.1 ha hj p.2 hD
      rw [hai] at h
      exact h
    · apply Finset.mem_union_right
      have h := far_coarseShape_mem X p.1 ha hj p.2 hD
      rw [hai] at h
      exact h
  have hcls : ∀ p ∈ S, ∀ p' ∈ S, coarseShape X p.1 p.2 = coarseShape X p'.1 p'.2 →
      ∀ c, s < R p c → s < R p' c := by
    intro p hp p' hp' hsh c hr
    have hbin : (X.g.L.stKey p.1).1 = (X.g.L.stKey p'.1).1 :=
      (hmemS p hp).2.1.trans (hmemS p' hp').2.1.symm
    have heq := coarseShape_rate_eq X (v, c) p.1 p'.1 hbin p.2 p'.2 hsh
    exact lt_of_lt_of_eq hr heq
  have hA : ∀ p ∈ S, (X.coarseLaw v).pr (fun c => s < R p c) ≤ q / s := by
    intro p hp
    obtain ⟨ha, _, hD⟩ := hmemS p hp
    exact pr_lt_le_of_expect_le _ _
      (fun c => expect_nonneg' _ _ fun Z => Lane_q_s06_stages.pr_nonneg _ _) s q hs (hmean p.1 ha p.2 hD)
  have hqs : 0 ≤ q / s := div_nonneg hq hs.le
  calc
    _ ≤ (X.coarseLaw v).pr (fun c => ∃ p ∈ S, s < R p c) := Lane_q_s06_stages.pr_mono _ hsub
    _ ≤ ∑ _k ∈ coarseShapeCodes X i, q / s :=
      pr_exists_code_le _ S _ (fun p => coarseShape X p.1 p.2) hU _ (fun _ => q / s) (fun _ _ => hqs)
        hcls hA
    _ = ((coarseShapeCodes X i).card : ℝ) * (q / s) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * (descriptorCodeCountBound X : ℝ) * (q / s) := by
      apply mul_le_mul_of_nonneg_right _ hqs
      exact_mod_cast coarseShapeCodes_card_le X i

/-! ### Eventual numerical budgets for the coarse charge `n^{-δ₁/8}` -/

open Filter in
theorem eventually_coarse_step2_tail (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∀ᶠ n : ℕ in atTop,
      8 * ((m₆ p₀ n : ℝ) + 1) * (n : ℝ) ^ (-(δ₂ / 8)) ≤ (n : ℝ) ^ (-(δ₁ / 8)) / 8 := by
  let a : ℝ := δ₂ / 128 - δ₁ / 8
  have ha : 0 < a := by norm_num [a, δ₂, δ₁]
  have hh := Lane_q_s06_stages.eventually_const_mul_nat_rpow_neg_lt (c := 2) ha
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_step2_group_charge_budget p₀ hp₀, hh, Filter.eventually_ge_atTop 2]
    with n hb hsmall hn2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have heq : (n : ℝ) ^ (-(δ₂ / 128)) = (n : ℝ) ^ (-a) * (n : ℝ) ^ (-(δ₁ / 8)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    dsimp [a]
    ring
  have hx : 0 ≤ (n : ℝ) ^ (-(δ₁ / 8)) := Real.rpow_nonneg hn0.le _
  have h2 : (n : ℝ) ^ (-(δ₂ / 128)) / 4 ≤ (n : ℝ) ^ (-(δ₁ / 8)) / 8 := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right (show (n : ℝ) ^ (-a) ≤ 1 / 2 by linarith) hx]
  exact hb.trans h2

open Filter in
theorem eventually_coarse_step3_tail :
    ∀ᶠ n : ℕ in atTop, 3 * (n : ℝ) ^ (-(1 / 10 ^ 7 : ℝ)) ≤ (n : ℝ) ^ (-(δ₁ / 8)) / 8 := by
  let a : ℝ := 1 / 10 ^ 7 - δ₁ / 8
  have ha : 0 < a := by norm_num [a, δ₁]
  have hh := Lane_q_s06_stages.eventually_const_mul_nat_rpow_neg_lt (c := 24) ha
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hh, Filter.eventually_ge_atTop 2] with n hsmall hn2
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have heq : (n : ℝ) ^ (-(1 / 10 ^ 7 : ℝ)) = (n : ℝ) ^ (-a) * (n : ℝ) ^ (-(δ₁ / 8)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    dsimp [a]
    ring
  rw [heq]
  have hx : 0 ≤ (n : ℝ) ^ (-(δ₁ / 8)) := Real.rpow_nonneg hn0.le _
  nlinarith [mul_le_mul_of_nonneg_right (show 24 * (n : ℝ) ^ (-a) ≤ 1 by linarith) hx]

end

end HypercubeRamsey.S06.Lane_opus_coarse
