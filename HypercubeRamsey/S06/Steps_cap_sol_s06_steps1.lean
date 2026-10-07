import HypercubeRamsey.S06.Steps_window_sol_s06_steps1

namespace HypercubeRamsey.S06.Lane_sol_s06_steps1
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

def capBudget (n : ℕ) : ℝ := (20 : ℝ)^603 * (n : ℝ)^(Dstar₆ + 602*d₀)

def candReference (h : X.Key) : FinProb (X.Bin → Fin N) :=
  FinProb.pi fun u => if u ∈ X.binsOf (X.C h) then secondMixture6 M else pointMass6 X.y₀

def tagReference (S : Finset X.Key) : FinProb (X.Key → X.ι) :=
  FinProb.pi fun s => if s ∈ S then tagLaw6 M else pointMass6 X.i₀

def boundaryReference (h : X.Key) : FinProb X.Coarse :=
  (candReference X h).bind fun _ => tagReference X (X.C h)

theorem clipped_weight {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (P : I → FinProb Ω) (S : Finset I) (z₀ : Ω) (z : I → Ω)
    (hz : ∀ i, i ∉ S → z i = z₀) :
    (FinProb.pi (fun i => if i ∈ S then P i else pointMass6 z₀)).w z = ∏ i ∈ S, (P i).w (z i) := by
  rw [← Fintype.prod_ite_mem S]
  change (∏ i, (if i ∈ S then P i else pointMass6 z₀).w (z i)) = _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [hi]
  · simp [hi, pointMass6, hz i hi]

theorem cap_factor_bound (hn : 1 ≤ (n : ℝ)) (r t : ℕ) (hr : r ≤ 602) (ht : t ≤ 602) :
    (20 : ℝ)^(r+1) * (n : ℝ)^Dstar₆ * ((n : ℝ)^d₀)^t ≤ capBudget n := by
  have hnp : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hd : 1 ≤ (n : ℝ)^d₀ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn (show (0 : ℝ) ≤ d₀ by norm_num [d₀])
  have h20 : (20 : ℝ)^(r+1) ≤ (20 : ℝ)^603 := pow_le_pow_right₀ (by norm_num) (by omega)
  have htag : ((n : ℝ)^d₀)^t ≤ ((n : ℝ)^d₀)^602 := pow_le_pow_right₀ hd ht
  calc
    _ ≤ (20 : ℝ)^603 * (n : ℝ)^Dstar₆ * ((n : ℝ)^d₀)^602 := by gcongr
    _ = capBudget n := by
      have hp602 : ((n : ℝ)^d₀)^(602 : ℕ) = (n : ℝ)^(602*d₀) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnp.le]
        congr 1 <;> norm_num <;> ring
      rw [hp602, mul_assoc, ← Real.rpow_add hnp]
      rfl

/-- The boundary joint likelihood is capped against mixture references for its candidate window. -/
theorem boundary_joint_cap (h : X.Key) (hn : 1 ≤ (n : ℝ))
    (hTag : ∀ pv k, pv.val (primaryName6 k) ∈ X.par.heavy →
      related6 E G M (pv.val (primaryName6 k)) (pv.val (otherPrimaryName6 k)) →
      ∀ i, (X.tagLawAt pv k).w i ≤ (n : ℝ)^d₀ * M.Λ i) (d : X.Coarse) (y : Fin N) :
    (N : ℝ) * (X.initLaw.w y *
      ((candWindow X h y).bind (fun A => tagWindow X (y,A) (X.C h))).w d) ≤
        capBudget n * (boundaryReference X h).w d := by
  let S := X.binsOf (X.C h)
  let T := X.C h
  let O := (candWindow X h y).bind (fun A => tagWindow X (y,A) T)
  have hR : 0 ≤ (boundaryReference X h).w d := (boundaryReference X h).nonneg d
  have hbudget : 0 ≤ capBudget n := by unfold capBudget; positivity
  by_cases hw : X.initLaw.w y * O.w d = 0
  · simpa [O, T, hw] using mul_nonneg hbudget hR
  · have hinit : 0 < X.initLaw.w y := lt_of_le_of_ne (X.initLaw.nonneg y) (Ne.symm (left_ne_zero_of_mul hw))
    have ho : O.w d ≠ 0 := right_ne_zero_of_mul hw
    have hc : (candWindow X h y).w d.1 ≠ 0 := left_ne_zero_of_mul ho
    have ht : (tagWindow X (y,d.1) T).w d.2 ≠ 0 := right_ne_zero_of_mul ho
    have hA := candWindow_supported X h y d.1 hc
    have hI := tagWindow_supported X (y,d.1) T d.2 ht
    have hmass : 0 < X.par.piPrime.pr (fun z => z ∈ X.par.S₀) := by linarith [X.par.S₀_mass]
    have hyS := (restrictOr6_supp hmass (ne_of_gt hinit)).1
    have hcpos : ∀ u ∈ S, 0 < (X.candLaw y).w (d.1 u) := by
      intro u hu
      have hp := Lane_q_s06_steps1.prod_pos_each6
        (fun u => (if u ∈ S then X.candLaw y else pointMass6 X.y₀).w (d.1 u))
        (fun u => (if u ∈ S then X.candLaw y else pointMass6 X.y₀).nonneg (d.1 u))
        (lt_of_le_of_ne ((candWindow X h y).nonneg d.1) (Ne.symm hc)) u
      simpa [hu] using hp
    have htag : ∀ k ∈ T, (X.tagLawAt (y,d.1) k).w (d.2 k) ≤ (n : ℝ)^d₀ * M.Λ (d.2 k) := by
      intro k hk
      have hbin : k.1 ∈ S := Finset.mem_image.mpr ⟨k,hk,rfl⟩
      have hp := Lane_q_s06_steps1.parent_heavy_related_of_local_support X k (y,d) hinit (hcpos k.1 hbin)
      exact hTag (y,d.1) k hp.1 hp.2 (d.2 k)
    have hcprod : (∏ u ∈ S, (X.candLaw y).w (d.1 u)) ≤
        (20 : ℝ)^S.card * ∏ u ∈ S, (secondMixture6 M).w (d.1 u) := by
      calc
        _ ≤ ∏ u ∈ S, 20 * (secondMixture6 M).w (d.1 u) := by
          apply Finset.prod_le_prod₀ (fun u _ => (X.candLaw y).nonneg _)
          intro u _
          exact X.par.partner_cap y hyS X.y₀ (d.1 u)
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    have htprod : (∏ k ∈ T, (X.tagLawAt (y,d.1) k).w (d.2 k)) ≤
        ((n : ℝ)^d₀)^T.card * ∏ k ∈ T, M.Λ (d.2 k) := by
      calc
        _ ≤ ∏ k ∈ T, (n : ℝ)^d₀ * M.Λ (d.2 k) :=
          Finset.prod_le_prod₀ (fun k _ => (X.tagLawAt (y,d.1) k).nonneg _) htag
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    have hprior : (N : ℝ) * X.initLaw.w y ≤ 20 * (n : ℝ)^Dstar₆ := by
      have hp := Lane_q_s06_steps1.initLaw_atom_cap6 X y
      have hnonneg := Real.rpow_nonneg (Nat.cast_nonneg n) Dstar₆
      nlinarith
    have hRc : (candReference X h).w d.1 = ∏ u ∈ S, (secondMixture6 M).w (d.1 u) :=
      clipped_weight _ S X.y₀ d.1 hA
    have hRt : (tagReference X T).w d.2 = ∏ k ∈ T, M.Λ (d.2 k) :=
      clipped_weight _ T X.i₀ d.2 hI
    have hcardT : T.card ≤ 602 := X.g.flips.key_neighborhood_card h
    have hcardS : S.card ≤ 602 := le_trans Finset.card_image_le hcardT
    have hcnonneg : 0 ≤ ∏ u ∈ S, (X.candLaw y).w (d.1 u) := Finset.prod_nonneg fun u _ => (X.candLaw y).nonneg _
    have hmixnonneg : 0 ≤ ∏ u ∈ S, (secondMixture6 M).w (d.1 u) := Finset.prod_nonneg fun u _ => (secondMixture6 M).nonneg _
    have htnonneg : 0 ≤ ∏ k ∈ T, (X.tagLawAt (y,d.1) k).w (d.2 k) := Finset.prod_nonneg fun k _ => (X.tagLawAt (y,d.1) k).nonneg _
    rw [show ((candWindow X h y).bind (fun A => tagWindow X (y,A) (X.C h))).w d =
      (candWindow X h y).w d.1 * (tagWindow X (y,d.1) T).w d.2 by rfl,
      candWindow_weight X h y d.1 hA, tagWindow_weight X (y,d.1) T d.2 hI]
    change (N : ℝ) * (X.initLaw.w y * _) ≤ capBudget n * ((candReference X h).w d.1 * (tagReference X T).w d.2)
    rw [hRc, hRt]
    calc
      _ = ((N : ℝ) * X.initLaw.w y) * (∏ u ∈ S, (X.candLaw y).w (d.1 u)) *
          (∏ k ∈ T, (X.tagLawAt (y,d.1) k).w (d.2 k)) := by ring
      _ ≤ (20 * (n : ℝ)^Dstar₆) * ((20 : ℝ)^S.card * ∏ u ∈ S, (secondMixture6 M).w (d.1 u)) *
          (((n : ℝ)^d₀)^T.card * ∏ k ∈ T, M.Λ (d.2 k)) := by gcongr <;> positivity
      _ = ((20 : ℝ)^(S.card+1) * (n : ℝ)^Dstar₆ * ((n : ℝ)^d₀)^T.card) *
          ((∏ u ∈ S, (secondMixture6 M).w (d.1 u)) * (∏ k ∈ T, M.Λ (d.2 k))) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (cap_factor_bound hn S.card T.card hcardS hcardT)
        (mul_nonneg (Finset.prod_nonneg fun u _ => (secondMixture6 M).nonneg _) (Finset.prod_nonneg fun k _ => M.Λ_nonneg _))


def tagBound : Prop := ∀ pv k, pv.val (primaryName6 k) ∈ X.par.heavy →
  related6 E G M (pv.val (primaryName6 k)) (pv.val (otherPrimaryName6 k)) →
  ∀ i, (X.tagLawAt pv k).w i ≤ (n : ℝ)^d₀ * M.Λ i

theorem interior_joint_cap (h : X.Key) (hf : h.2 = .interior) (hn : 1 ≤ (n : ℝ))
    (hTag : tagBound X) (v : Fin N) (hv : 0 < X.initLaw.w v)
    (A₀ : X.Bin → Fin N) (I : X.Key → X.ι) (y : Fin N) :
    (N : ℝ) * ((X.candLaw v).w y *
      (tagWindow X (v,Function.update A₀ h.1 y) (X.C h)).w I) ≤
        capBudget n * (tagReference X (X.C h)).w I := by
  let pv : Par6 X.Bin N := (v,Function.update A₀ h.1 y)
  let T := X.C h
  have hbudget : 0 ≤ capBudget n := by unfold capBudget; positivity
  by_cases hw : (X.candLaw v).w y * (tagWindow X pv T).w I = 0
  · simpa only [pv, T, hw, mul_zero] using
      mul_nonneg hbudget ((tagReference X (X.C h)).nonneg I)
  · have hc : 0 < (X.candLaw v).w y :=
      lt_of_le_of_ne ((X.candLaw v).nonneg y) (Ne.symm (left_ne_zero_of_mul hw))
    have ht : (tagWindow X pv T).w I ≠ 0 := right_ne_zero_of_mul hw
    have hI := tagWindow_supported X pv T I ht
    have hmass : 0 < X.par.piPrime.pr (fun z => z ∈ X.par.S₀) := by linarith [X.par.S₀_mass]
    have hvS := (restrictOr6_supp hmass (ne_of_gt hv)).1
    have hprior := Lane_q_s06_steps1.candLaw_atom_cap6 X v y hvS
    have htag : ∀ k ∈ T, (X.tagLawAt pv k).w (I k) ≤ (n : ℝ)^d₀ * M.Λ (I k) := by
      intro k hk
      have hbin := Lane_q_s06_steps1.keyNeighbor_bin_eq_of_interior6 binAdjacent6 h k hk hf
      have hck : 0 < (X.candLaw v).w ((Function.update A₀ h.1 y) k.1) := by simpa [hbin] using hc
      have hp := Lane_q_s06_steps1.parent_heavy_related_of_local_support X k (v,Function.update A₀ h.1 y,I) hv hck
      exact hTag pv k hp.1 hp.2 (I k)
    have htprod : (∏ k ∈ T, (X.tagLawAt pv k).w (I k)) ≤
        ((n : ℝ)^d₀)^T.card * ∏ k ∈ T, M.Λ (I k) := by
      calc
        _ ≤ ∏ k ∈ T, (n : ℝ)^d₀ * M.Λ (I k) :=
          Finset.prod_le_prod₀ (fun k _ => (X.tagLawAt pv k).nonneg _) htag
        _ = _ := by rw [Finset.prod_mul_distrib]; simp
    have hRt : (tagReference X T).w I = ∏ k ∈ T, M.Λ (I k) := clipped_weight _ T X.i₀ I hI
    have htnonneg : 0 ≤ ∏ k ∈ T, (X.tagLawAt pv k).w (I k) := Finset.prod_nonneg fun k _ => (X.tagLawAt pv k).nonneg _
    rw [tagWindow_weight X pv T I hI, hRt]
    calc
      _ = ((N : ℝ) * (X.candLaw v).w y) * ∏ k ∈ T, (X.tagLawAt pv k).w (I k) := by ring
      _ ≤ (20 * (n : ℝ)^Dstar₆) * (((n : ℝ)^d₀)^T.card * ∏ k ∈ T, M.Λ (I k)) := by gcongr <;> positivity
      _ = ((20 : ℝ)^(0+1) * (n : ℝ)^Dstar₆ * ((n : ℝ)^d₀)^T.card) * ∏ k ∈ T, M.Λ (I k) := by norm_num; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (cap_factor_bound hn 0 T.card (by omega) (X.g.flips.key_neighborhood_card h))
        (Finset.prod_nonneg fun k _ => M.Λ_nonneg _)

/-- Cap failure in the boundary raw experiment. -/
theorem boundary_cap_bound (h : X.Key) (hf : h.2 = .boundary) (hn : 1 ≤ (n : ℝ))
    (hTag : tagBound X) (t : ℝ) (ht : 0 < t) :
    X.baseLaw.pr (fun b => ∃ z, t < (N : ℝ) * (X.hidPost b h).w z) ≤ capBudget n / t := by
  let O (y : Fin N) := (candWindow X h y).bind fun A => tagWindow X (y,A) (X.C h)
  let A (y : Fin N) (d : X.Coarse) := ∃ z, t < (N : ℝ) * (X.hidPost (y,d) h).w z
  have hpost (y : Fin N) (d : X.Coarse) (hw : X.initLaw.w y * (O y).w d ≠ 0) :
      X.hidPost (y,d) h = normalize6 (fun z => X.initLaw.w z * (O z).w d) X.y₀ := by
    have ho : (O y).w d ≠ 0 := right_ne_zero_of_mul hw
    have hc := candWindow_supported X h y d.1 (left_ne_zero_of_mul ho)
    have hi := tagWindow_supported X (y,d.1) (X.C h) d.2 (right_ne_zero_of_mul ho)
    unfold Ctx6.hidPost
    congr 1
    funext z
    change X.hidWeight (y,d) h (X.C h) z = X.initLaw.w z *
      ((candWindow X h z).w d.1 * (tagWindow X (z,d.1) (X.C h)).w d.2)
    rw [candWindow_weight X h z d.1 hc, tagWindow_weight X (z,d.1) _ d.2 hi]
    simp [Ctx6.hidWeight, Ctx6.parOf, primaryName6, hf, Par6.set, mul_assoc]
  have hb : ∑ y, X.initLaw.w y * (O y).pr (A y) ≤ capBudget n / t :=
    bayes_cap_experiment X.initLaw O (boundaryReference X h) X.y₀ A (N : ℝ) (capBudget n) t
      (by unfold capBudget; positivity) ht (fun d y => boundary_joint_cap X h hn hTag d y)
      (fun y d hw ha => by simpa only [A, hpost y d hw] using ha)
  let F (b : X.Base) : ℝ := if ∃ z, t < (N : ℝ) * (X.hidPost b h).w z then 1 else 0
  have hF : ∀ (v : Fin N) (V V' : X.Bin → Fin N) (I I' : X.Key → X.ι),
      (∀ u ∈ X.binsOf (X.C h), V u = V' u) → (∀ k ∈ X.C h, I k = I' k) → F (v,V,I) = F (v,V',I') := by
    intro v V V' I I' hV hI
    have hp : X.hidPost (v,V,I) h = X.hidPost (v,V',I') h := by
      unfold Ctx6.hidPost
      congr 1
      funext z
      exact hidWeight_local X h _ (fun _ hx => hx) (v,V,I) (v,V',I') (fun _ => rfl) (fun _ => hV) hI z
    simp only [F, hp]
  have heq : X.baseLaw.pr (fun b => ∃ z, t < (N : ℝ) * (X.hidPost b h).w z) =
      ∑ y, X.initLaw.w y * (O y).pr (A y) := by
    have hrepr : X.baseLaw.pr (fun b => ∃ z, t < (N : ℝ) * (X.hidPost b h).w z) = X.baseLaw.expect F := by
      unfold FinProb.pr FinProb.expect
      apply Finset.sum_congr rfl
      intro b _
      simp [F, mul_ite]
    rw [hrepr, base_expect_window X h F hF]
    change (X.initLaw.bind O).expect (fun b => F (b.1,b.2)) = _
    rw [FinProb.bind_expect X.initLaw O (fun y d => F (y,d))]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro d _
    simp [F, A, mul_ite]
  rw [heq]
  exact hb


/-- Cap failure in the interior raw experiment. -/
theorem interior_cap_bound (h : X.Key) (hf : h.2 = .interior) (hn : 1 ≤ (n : ℝ))
    (hTag : tagBound X) (t : ℝ) (ht : 0 < t) :
    X.baseLaw.pr (fun b => ∃ z, t < (N : ℝ) * (X.hidPost b h).w z) ≤ capBudget n / t := by
  let A₀ : X.Bin → Fin N := fun _ => X.y₀
  let F (b : X.Base) : ℝ := if ∃ z, t < (N : ℝ) * (X.hidPost b h).w z then 1 else 0
  have hFsame (v : Fin N) (A A' : X.Bin → Fin N) (I : X.Key → X.ι) : F (v,A,I) = F (v,A',I) := by
    have hp : X.hidPost (v,A,I) h = X.hidPost (v,A',I) h := by
      unfold Ctx6.hidPost
      congr 1
      funext z
      exact hidWeight_local X h _ (fun _ hx => hx) (v,A,I) (v,A',I) (fun _ => rfl) (by simp [hf]) (fun _ _ => rfl) z
    simp only [F, hp]
  have hFlocal : ∀ (v : Fin N) (A A' : X.Bin → Fin N) (I I' : X.Key → X.ι),
      (∀ u ∈ X.binsOf (X.C h), A u = A' u) → (∀ k ∈ X.C h, I k = I' k) → F (v,A,I) = F (v,A',I') := by
    intro v A A' I I' _ hI
    have hp : X.hidPost (v,A,I) h = X.hidPost (v,A',I') h := by
      unfold Ctx6.hidPost
      congr 1
      funext z
      exact hidWeight_local X h _ (fun _ hx => hx) (v,A,I) (v,A',I') (fun _ => rfl) (by simp [hf]) hI z
    simp only [F, hp]
  let g (v : Fin N) (A : X.Bin → Fin N) := (tagWindow X (v,A) (X.C h)).expect (fun I => F (v,A,I))
  have hg (v : Fin N) : FinProb.DependsOn (g v) {h.1} := by
    intro A A' hA
    have hAA : A h.1 = A' h.1 := hA h.1 (Finset.mem_singleton_self _)
    have hlaw : tagWindow X (v,A) (X.C h) = tagWindow X (v,A') (X.C h) := by
      unfold tagWindow
      congr 1
      funext k
      by_cases hk : k ∈ X.C h
      · simp only [hk, ite_true]
        exact Lane_q_s06_steps1.tagLawAt_eq_of_local_interior6 X h k hk hf v A A' hAA
      · simp [hk]
    unfold g
    rw [hlaw]
    unfold FinProb.expect
    apply Finset.sum_congr rfl
    intro I _
    dsimp only
    rw [hFsame v A A' I]
  have hself : h ∈ X.C h := by simp [Ctx6.C, keyNeighborhood6, keyAdjacent6]
  have hbin : h.1 ∈ X.binsOf (X.C h) := Finset.mem_image.mpr ⟨h,hself,rfl⟩
  have hcond (v : Fin N) (hv : 0 < X.initLaw.w v) : (candWindow X h v).expect (g v) ≤ capBudget n / t := by
    let pv (y : Fin N) : Par6 X.Bin N := (v,Function.update A₀ h.1 y)
    let O (y : Fin N) := tagWindow X (pv y) (X.C h)
    let A (_y : Fin N) (I : X.Key → X.ι) := ∃ z, t < (N : ℝ) * (X.hidPost (v,A₀,I) h).w z
    have hpost (y : Fin N) (I : X.Key → X.ι) (hw : (X.candLaw v).w y * (O y).w I ≠ 0) :
        X.hidPost (v,A₀,I) h = normalize6 (fun z => (X.candLaw v).w z * (O z).w I) X.y₀ := by
      have hi := tagWindow_supported X (pv y) (X.C h) I (right_ne_zero_of_mul hw)
      unfold Ctx6.hidPost
      congr 1
      funext z
      change X.hidWeight (v,A₀,I) h (X.C h) z = (X.candLaw v).w z * (tagWindow X (pv z) (X.C h)).w I
      rw [tagWindow_weight X (pv z) _ I hi]
      simp [Ctx6.hidWeight, Ctx6.parOf, primaryName6, hf, Par6.set, pv]
    have hb : ∑ y, (X.candLaw v).w y * (O y).pr (A y) ≤ capBudget n / t :=
      bayes_cap_experiment (X.candLaw v) O (tagReference X (X.C h)) X.y₀ A (N : ℝ) (capBudget n) t
        (by unfold capBudget; positivity) ht (fun I y => interior_joint_cap X h hf hn hTag v hv A₀ I y)
        (fun y I hw ha => by simpa only [A, hpost y I hw] using ha)
    have heq : (candWindow X h v).expect (g v) = ∑ y, (X.candLaw v).w y * (O y).pr (A y) := by
      unfold candWindow
      rw [pi_expect_single _ h.1 A₀ (g v) (hg v)]
      change (if h.1 ∈ X.binsOf (X.C h) then X.candLaw v else pointMass6 X.y₀).expect
        (fun y => g v (Function.update A₀ h.1 y)) = _
      rw [if_pos hbin]
      unfold FinProb.expect FinProb.pr
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      change (tagWindow X (pv y) (X.C h)).expect (fun I => F (v,Function.update A₀ h.1 y,I)) = _
      unfold FinProb.expect
      apply Finset.sum_congr rfl
      intro I _
      dsimp only
      rw [hFsame v (Function.update A₀ h.1 y) A₀ I]
      simp [F, A, O, mul_ite]
    rw [heq]
    exact hb
  have hrepr : X.baseLaw.pr (fun b => ∃ z, t < (N : ℝ) * (X.hidPost b h).w z) = X.baseLaw.expect F := by
    unfold FinProb.pr FinProb.expect
    apply Finset.sum_congr rfl
    intro b _
    simp [F, mul_ite]
  rw [hrepr, base_expect_window X h F hFlocal]
  change (X.initLaw.bind (fun v => (candWindow X h v).bind fun A => tagWindow X (v,A) (X.C h))).expect
    (fun b => F (b.1,b.2)) ≤ capBudget n / t
  rw [FinProb.bind_expect _ _ (fun v d => F (v,d))]
  calc
    _ = ∑ v, X.initLaw.w v * (candWindow X h v).expect (g v) := by
      apply Finset.sum_congr rfl
      intro v _
      congr 1
      exact FinProb.bind_expect _ _ (fun A I => F (v,A,I))
    _ ≤ ∑ v, X.initLaw.w v * (capBudget n / t) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : X.initLaw.w v = 0
      · simp [hv]
      · exact mul_le_mul_of_nonneg_left (hcond v (lt_of_le_of_ne (X.initLaw.nonneg v) (Ne.symm hv))) (X.initLaw.nonneg v)
    _ = capBudget n / t := by rw [← Finset.sum_mul, X.initLaw.sum_eq_one, one_mul]

theorem posterior_cap_bound (h : X.Key) (hn : 1 ≤ (n : ℝ)) (hTag : tagBound X) (t : ℝ) (ht : 0 < t) :
    X.baseLaw.pr (fun b => ∃ z, t < (N : ℝ) * (X.hidPost b h).w z) ≤ capBudget n / t := by
  cases hf : h.2
  · exact interior_cap_bound X h hf hn hTag t ht
  · exact boundary_cap_bound X h hf hn hTag t ht

end
end HypercubeRamsey.S06.Lane_sol_s06_steps1
