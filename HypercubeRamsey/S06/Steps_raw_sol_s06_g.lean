import HypercubeRamsey.S06.Steps_sol_s06_g
import HypercubeRamsey.S06.Steps_local_sol_s06_steps1

namespace HypercubeRamsey.S06.Lane_sol_s06_g
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

/-- The gate may depend on observations generated before the tuple outcomes. -/
theorem observation_gate_mixture_bound {Ξ Ω : Type*} [Fintype Ξ] [Fintype Ω]
    (π : FinProb Ξ) (Q : FinProb Ω) (P : Ξ → FinProb Ω)
    (gate : Ξ → Ω → Prop) (lik : Ξ → Ω → ℝ) (m θ : Ω → ℝ) (ε : ℝ)
    (hm : ∀ ω, m ω = ∑ ξ, if gate ξ ω then π.w ξ * lik ξ ω else 0)
    (hdom : ∀ ξ ω, gate ξ ω → (P ξ).w ω ≤ Q.w ω * lik ξ ω)
    (hsmall : (∑ ω, if m ω < θ ω then Q.w ω * m ω else 0) ≤ ε) :
    ∑ ξ, π.w ξ * (P ξ).pr (fun ω => gate ξ ω ∧ m ω < θ ω) ≤ ε := by
  classical
  calc
    _ ≤ ∑ ξ, π.w ξ * ∑ ω, if gate ξ ω ∧ m ω < θ ω then Q.w ω * lik ξ ω else 0 := by
      apply Finset.sum_le_sum
      intro ξ hξ
      apply mul_le_mul_of_nonneg_left _ (π.nonneg ξ)
      unfold FinProb.pr
      apply Finset.sum_le_sum
      intro ω hω
      by_cases he : gate ξ ω ∧ m ω < θ ω
      · simp only [if_pos he]
        exact hdom ξ ω he.1
      · simp only [if_neg he]
        rfl
    _ = ∑ ω, if m ω < θ ω then Q.w ω * m ω else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hlt : m ω < θ ω
      · simp only [hlt, and_true, if_true]
        rw [hm ω, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ hξ
        by_cases hg : gate ξ ω
        · simp only [if_pos hg]
          ring
        · simp [hg]
      · simp [hlt]
    _ ≤ ε := hsmall

private theorem ratio_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ safeRatio6 a b := by
  unfold safeRatio6
  split
  · exact le_rfl
  · exact div_nonneg ha hb

private theorem ratio_weight_le {a b : ℝ} (ha : 0 ≤ a) : b * safeRatio6 a b ≤ a := by
  unfold safeRatio6
  by_cases hb : b = 0
  · simp [hb, ha]
  · simp [hb, mul_div_cancel₀]

private theorem tuple_weight {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (S : Finset X.Name)
    (T : FinProb X.ι) (o : X.Tuple) :
    (X.tupleLawOn H S T).w o = T.w o.1 * ∏ r, (X.labelLaw H S o.1).w (o.2 r) := by
  simp [Ctx6.tupleLawOn, FinProb.bind, FinProb.pi]

/-- A likelihood ratio never creates mass outside its reference support. -/
theorem high_lik_integral_le_one {γ p₀ K : ℝ} {n N : ℕ}
    {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
    (X : Ctx6 γ p₀ K n N E G M) (H : X.Hist) (b : X.State) (β : X.Ty) (ξ : Fin N) :
    ∑ o, (X.highRef H b β).w o * X.highLik H b ξ β o ≤ 1 := by
  let Hξ := X.withParH H (X.tgtName b) ξ
  let S := (reqNames6 β).erase (.par (X.tgtName b))
  let T := X.Tβ Hξ β
  have hpoint (o : X.Tuple) : (X.highRef H b β).w o * X.highLik H b ξ β o ≤
      (X.tupleLaw Hξ β).w o := by
    let Qr (r : Fin X.k) := (X.labelLaw H S o.1).w (o.2 r)
    let Pr (r : Fin X.k) := (X.labelLaw Hξ (reqNames6 β) o.1).w (o.2 r)
    have htag : M.Λ o.1 * safeRatio6 (T.w o.1) (M.Λ o.1) ≤ T.w o.1 :=
      ratio_weight_le (T.nonneg _)
    have hlabel : (∏ r, Qr r * safeRatio6 (Pr r) (Qr r)) ≤ ∏ r, Pr r :=
      Finset.prod_le_prod₀
        (fun r hr => mul_nonneg ((X.labelLaw H S o.1).nonneg _)
          (ratio_nonneg ((X.labelLaw Hξ (reqNames6 β) o.1).nonneg _) ((X.labelLaw H S o.1).nonneg _)))
        (fun r hr => ratio_weight_le ((X.labelLaw Hξ (reqNames6 β) o.1).nonneg _))
    have hraw := tuple_weight X Hξ (reqNames6 β) T o
    have href := tuple_weight X H S (tagLaw6 M) o
    change (X.tupleLawOn H S (tagLaw6 M)).w o * _ ≤ (X.tupleLawOn Hξ (reqNames6 β) T).w o
    rw [href, hraw]
    unfold Ctx6.highLik Ctx6.tupleRatio
    change (M.Λ o.1 * ∏ r, Qr r) * (safeRatio6 (T.w o.1) (M.Λ o.1) * ∏ r, safeRatio6 (Pr r) (Qr r)) ≤ _
    calc
      _ = (M.Λ o.1 * safeRatio6 (T.w o.1) (M.Λ o.1)) *
          ∏ r, Qr r * safeRatio6 (Pr r) (Qr r) := by rw [Finset.prod_mul_distrib]; ring
      _ ≤ T.w o.1 * ∏ r, Pr r := mul_le_mul htag hlabel
        (Finset.prod_nonneg fun r hr => mul_nonneg ((X.labelLaw H S o.1).nonneg _)
          (ratio_nonneg ((X.labelLaw Hξ (reqNames6 β) o.1).nonneg _) ((X.labelLaw H S o.1).nonneg _)))
        (T.nonneg _)
  exact (Finset.sum_le_sum fun o ho => hpoint o).trans (le_of_eq (X.tupleLaw Hξ β).sum_eq_one)

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)

/-- The primitive observations read by the high-target local model. -/
def LocalAgree {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist) : Prop :=
  (nm ≠ .initial → H.1.1 = H'.1.1) ∧
    (∀ u ∈ X.locBins D nm, H.1.2.1 u = H'.1.2.1 u) ∧
    (∀ s ∈ X.locKeys D, H.1.2.2 s = H'.1.2.2 s) ∧
    ∀ ℓ ∈ X.locHid D, H.2 ℓ = H'.2 ℓ

theorem substituted_initial_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) :
    (X.withParH H nm ξ).1.1 = (X.withParH H' nm ξ).1.1 := by
  cases nm with
  | initial => rfl
  | candidate u => exact h.1 (by simp)

theorem substituted_candidate_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (u : X.Bin) (hu : u ∈ X.binsOf (X.locKeys D)) :
    (X.withParH H nm ξ).1.2.1 u = (X.withParH H' nm ξ).1.2.1 u := by
  cases nm with
  | initial => exact h.2.1 u (Finset.mem_filter.mpr ⟨hu, by simp⟩)
  | candidate v =>
    by_cases huv : u = v
    · subst u
      simp [Ctx6.withParH, Ctx6.withPar, Ctx6.parOf, Par6.set]
    · have hmem : u ∈ X.locBins D (.candidate v) :=
        Finset.mem_filter.mpr ⟨hu, by simpa using huv⟩
      simpa [Ctx6.withParH, Ctx6.withPar, Ctx6.parOf, Par6.set, huv] using h.2.1 u hmem

theorem substituted_tag_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (s : X.Key) (hs : s ∈ X.locKeys D) :
    (X.withParH H nm ξ).1.2.2 s = (X.withParH H' nm ξ).1.2.2 s := h.2.2.1 s hs

theorem hidden_weight_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D)
    (S : Finset X.Key) (hS : S ⊆ X.C ℓ.1) (y : Fin N) :
    X.hidWeight (X.withParH H nm ξ).1 ℓ.1 S y =
      X.hidWeight (X.withParH H' nm ξ).1 ℓ.1 S y := by
  have hC : X.C ℓ.1 ⊆ X.locKeys D := by
    intro s hs
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨ℓ, hℓ, hs⟩)
  have hBins : X.binsOf (X.C ℓ.1) ⊆ X.binsOf (X.locKeys D) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨s, hs, rfl⟩
    exact Finset.mem_image.mpr ⟨s, hC hs, rfl⟩
  exact Lane_sol_s06_steps1.hidWeight_local X ℓ.1 S hS _ _
    (fun _ => substituted_initial_eq X nm D H H' h ξ)
    (fun _ u hu => substituted_candidate_eq X nm D H H' h ξ u (hBins hu))
    (fun s hs => substituted_tag_eq X nm D H H' h ξ s (hC (hS hs))) y

theorem hidden_post_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D) :
    X.hidPost (X.withParH H nm ξ).1 ℓ.1 = X.hidPost (X.withParH H' nm ξ).1 ℓ.1 := by
  unfold Ctx6.hidPost
  congr 1
  funext y
  exact hidden_weight_local_eq X nm D H H' h ξ ℓ hℓ _ (Finset.Subset.refl _) y


 theorem localAgree_withTag {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (q : X.Key) (i : X.ι) :
    LocalAgree X nm D (X.withTag H.1 q i, H.2) (X.withTag H'.1 q i, H'.2) := by
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro s hs
  by_cases hsq : s = q
  · subst s
    simp [Ctx6.withTag]
  · simp only [Ctx6.withTag, Function.update_of_ne hsq]
    exact h.2.2.1 s hs

 theorem hidden_rep_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D)
    (q : X.Key) (i : X.ι) :
    X.hidPostRep (X.withParH H nm ξ).1 ℓ.1 q i =
      X.hidPostRep (X.withParH H' nm ξ).1 ℓ.1 q i := by
  exact hidden_post_local_eq X nm D (X.withTag H.1 q i, H.2) (X.withTag H'.1 q i, H'.2)
    (localAgree_withTag X nm D H H' h q i) ξ ℓ hℓ

 theorem hidden_del_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D)
    (q : X.Key) :
    X.hidPostDel (X.withParH H nm ξ).1 ℓ.1 q =
      X.hidPostDel (X.withParH H' nm ξ).1 ℓ.1 q := by
  unfold Ctx6.hidPostDel
  congr 1
  funext y
  exact hidden_weight_local_eq X nm D H H' h ξ ℓ hℓ _ (Finset.erase_subset _ _) y

 theorem step1_local_iff {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D) :
    X.Step1OK (X.withParH H nm ξ).1 ℓ.1 ↔ X.Step1OK (X.withParH H' nm ξ).1 ℓ.1 := by
  have hp := hidden_post_local_eq X nm D H H' h ξ ℓ hℓ
  have hd (s : X.Key) := hidden_del_local_eq X nm D H H' h ξ ℓ hℓ s
  simp only [Ctx6.Step1OK, Ctx6.Step1Cap, Ctx6.Step1Del, hp, hd]


 theorem tag_law_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (s : X.Key) (hs : s ∈ X.locKeys D) :
    X.tagLawAt (X.parOf (X.withParH H nm ξ).1) s =
      X.tagLawAt (X.parOf (X.withParH H' nm ξ).1) s := by
  have hinit := substituted_initial_eq X nm D H H' h ξ
  have hbin := substituted_candidate_eq X nm D H H' h ξ s.1 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  cases hf : s.2 <;>
    simp only [Ctx6.tagLawAt, primaryName6, otherPrimaryName6, hf, Ctx6.parOf, Par6.val, hinit, hbin]

 theorem tag_gate_local_iff {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (e : Id × X.Ty) (he : e ∈ D) (i : X.ι) :
    X.tagGate (X.withParH H nm ξ).1 e.2 i ↔ X.tagGate (X.withParH H' nm ξ).1 e.2 i := by
  have hobs (ℓ : X.HKey) (hℓ : ℓ ∈ e.2.obs) : ℓ ∈ X.locHid D :=
    Finset.mem_biUnion.mpr ⟨e, he, hℓ⟩
  constructor
  · intro hg ℓ hℓ y
    have hr := hidden_rep_local_eq X nm D H H' h ξ ℓ (hobs ℓ hℓ) e.2.key i
    have hd := hidden_del_local_eq X nm D H H' h ξ ℓ (hobs ℓ hℓ) e.2.key
    rw [← hr, ← hd]
    exact hg ℓ hℓ y
  · intro hg ℓ hℓ y
    have hr := hidden_rep_local_eq X nm D H H' h ξ ℓ (hobs ℓ hℓ) e.2.key i
    have hd := hidden_del_local_eq X nm D H H' h ξ ℓ (hobs ℓ hℓ) e.2.key
    rw [hr, hd]
    exact hg ℓ hℓ y

 theorem tag_weight_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (e : Id × X.Ty) (he : e ∈ D)
    (S : Finset X.HKey) (hS : S ⊆ e.2.obs) (i : X.ι) :
    X.tagWeight (X.withParH H nm ξ) e.2 S i = X.tagWeight (X.withParH H' nm ξ) e.2 S i := by
  have hkey : e.2.key ∈ X.locKeys D :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hlaw := tag_law_local_eq X nm D H H' h ξ e.2.key hkey
  have hgate := propext (tag_gate_local_iff X nm D H H' h ξ e he i)
  unfold Ctx6.tagWeight
  rw [hlaw, hgate]
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  have hloc : ℓ ∈ X.locHid D := Finset.mem_biUnion.mpr ⟨e, he, hS hℓ⟩
  rw [hidden_rep_local_eq X nm D H H' h ξ ℓ hloc e.2.key i,
    hidden_del_local_eq X nm D H H' h ξ ℓ hloc e.2.key]
  exact congrArg (fun y => safeRatio6
    ((X.hidPostRep (X.withParH H' nm ξ).1 ℓ.1 e.2.key i).w y)
    ((X.hidPostDel (X.withParH H' nm ξ).1 ℓ.1 e.2.key).w y)) (h.2.2.2 ℓ hloc)

 theorem tag_mass_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (e : Id × X.Ty) (he : e ∈ D)
    (S : Finset X.HKey) (hS : S ⊆ e.2.obs) :
    X.tagMass (X.withParH H nm ξ) e.2 S = X.tagMass (X.withParH H' nm ξ) e.2 S := by
  unfold Ctx6.tagMass
  exact Finset.sum_congr rfl (fun i hi => tag_weight_local_eq X nm D H H' h ξ e he S hS i)

 theorem step2_local_iff {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (e : Id × X.Ty) (he : e ∈ D) :
    X.Step2Tests (X.withParH H nm ξ) e.2 ↔ X.Step2Tests (X.withParH H' nm ξ) e.2 := by
  have hf := tag_mass_local_eq X nm D H H' h ξ e he _ (Finset.Subset.refl _)
  have hd (ℓ : X.HKey) := tag_mass_local_eq X nm D H H' h ξ e he (e.2.obs.erase ℓ) (Finset.erase_subset ℓ e.2.obs)
  simp only [Ctx6.Step2Tests, hf, hd]

 theorem prior_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') : X.priorOf H nm = X.priorOf H' nm := by
  cases nm with
  | initial => rfl
  | candidate u => exact congrArg X.candLaw (h.1 (by simp))

 theorem high_gate_local_iff {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X (X.tgtName b) D H H') (ξ : Fin N) :
    X.HighGate H b D ξ ↔ X.HighGate H' b D ξ := by
  have hp := prior_local_eq X (X.tgtName b) D H H' h
  constructor
  · rintro ⟨hprior, h1, h2⟩
    refine ⟨by simpa only [hp] using hprior, ?_, ?_⟩
    · intro ℓ hℓ
      exact (step1_local_iff X (X.tgtName b) D H H' h ξ ℓ hℓ).mp (h1 ℓ hℓ)
    · intro e he
      exact (step2_local_iff X (X.tgtName b) D H H' h ξ e he).mp (h2 e he)
  · rintro ⟨hprior, h1, h2⟩
    refine ⟨by simpa only [hp] using hprior, ?_, ?_⟩
    · intro ℓ hℓ
      exact (step1_local_iff X (X.tgtName b) D H H' h ξ ℓ hℓ).mpr (h1 ℓ hℓ)
    · intro e he
      exact (step2_local_iff X (X.tgtName b) D H H' h ξ e he).mpr (h2 e he)


 theorem loc_density_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) :
    X.locDensity H nm D ξ = X.locDensity H' nm D ξ := by
  have hc : (∏ u ∈ X.locBins D nm,
      (N : ℝ) * (X.candLaw (X.withParH H nm ξ).1.1).w (H.1.2.1 u)) =
      ∏ u ∈ X.locBins D nm, (N : ℝ) * (X.candLaw (X.withParH H' nm ξ).1.1).w (H'.1.2.1 u) := by
    apply Finset.prod_congr rfl
    intro u hu
    rw [substituted_initial_eq X nm D H H' h ξ, h.2.1 u hu]
  have ht : (∏ s ∈ X.locKeys D,
      safeRatio6 ((X.tagLawAt (X.parOf (X.withParH H nm ξ).1) s).w (H.1.2.2 s)) (M.Λ (H.1.2.2 s))) =
      ∏ s ∈ X.locKeys D,
      safeRatio6 ((X.tagLawAt (X.parOf (X.withParH H' nm ξ).1) s).w (H'.1.2.2 s)) (M.Λ (H'.1.2.2 s)) := by
    apply Finset.prod_congr rfl
    intro s hs
    rw [tag_law_local_eq X nm D H H' h ξ s hs, h.2.2.1 s hs]
  have hz : (∏ ℓ ∈ X.locHid D,
      (N : ℝ) * (X.hidPost (X.withParH H nm ξ).1 ℓ.1).w (H.2 ℓ)) =
      ∏ ℓ ∈ X.locHid D, (N : ℝ) * (X.hidPost (X.withParH H' nm ξ).1 ℓ.1).w (H'.2 ℓ) := by
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [hidden_post_local_eq X nm D H H' h ξ ℓ hℓ, h.2.2.2 ℓ hℓ]
  dsimp only [Ctx6.withParH] at hc ht hz
  dsimp only [Ctx6.locDensity]
  rw [hc, ht, hz]


 theorem tag_post_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (e : Id × X.Ty) (he : e ∈ D) :
    X.Tβ (X.withParH H nm ξ) e.2 = X.Tβ (X.withParH H' nm ξ) e.2 := by
  unfold Ctx6.Tβ Ctx6.tagPost
  congr 1
  funext i
  exact tag_weight_local_eq X nm D H H' h ξ e he _ (Finset.Subset.refl _) i

 theorem substituted_primary_value_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (s : X.Key) (hs : s ∈ X.locKeys D) :
    X.varVal (X.withParH H nm ξ) (.par (primaryName6 s)) =
      X.varVal (X.withParH H' nm ξ) (.par (primaryName6 s)) := by
  have hinit := substituted_initial_eq X nm D H H' h ξ
  have hbin := substituted_candidate_eq X nm D H H' h ξ s.1 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  cases hf : s.2 <;> simp only [Ctx6.varVal, Ctx6.parOf, primaryName6, hf, Par6.val, hinit, hbin]

 theorem substituted_opposite_value_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (s : X.Key) (hs : s ∈ X.locKeys D) :
    X.varVal (X.withParH H nm ξ) (.par (otherPrimaryName6 s)) =
      X.varVal (X.withParH H' nm ξ) (.par (otherPrimaryName6 s)) := by
  have hinit := substituted_initial_eq X nm D H H' h ξ
  have hbin := substituted_candidate_eq X nm D H H' h ξ s.1 (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  cases hf : s.2 <;> simp only [Ctx6.varVal, Ctx6.parOf, otherPrimaryName6, hf, Par6.val, hinit, hbin]

 theorem required_values_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (ξ : Fin N) (e : Id × X.Ty) (he : e ∈ D)
    (v : X.Name) (hv : v ∈ reqNames6 e.2) :
    X.varVal (X.withParH H nm ξ) v = X.varVal (X.withParH H' nm ξ) v := by
  have hkey : e.2.key ∈ X.locKeys D := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  cases v with
  | hid ℓ =>
    have hobs : ℓ ∈ e.2.obs := by
      by_cases hm : e.2.mode = .high <;> simpa [reqNames6, hm] using hv
    exact h.2.2.2 ℓ (Finset.mem_biUnion.mpr ⟨e, he, hobs⟩)
  | par p =>
    have hp : p = primaryName6 e.2.key ∨ p = otherPrimaryName6 e.2.key := by
      by_cases hm : e.2.mode = .high
      · simpa [reqNames6, hm] using hv
      · exact Or.inl (by simpa [reqNames6, hm] using hv)
    rcases hp with rfl | rfl
    · exact substituted_primary_value_eq X nm D H H' h ξ e.2.key hkey
    · exact substituted_opposite_value_eq X nm D H H' h ξ e.2.key hkey

 theorem substituted_other_value (H : X.Hist) (nm : ParentName6 X.Bin) (ξ : Fin N)
    (v : X.Name) (hv : v ≠ .par nm) : X.varVal (X.withParH H nm ξ) v = X.varVal H v := by
  cases v with
  | hid ℓ => rfl
  | par p =>
    cases nm with
    | initial => cases p with
      | initial => exact False.elim (hv rfl)
      | candidate u => rfl
    | candidate u => cases p with
      | initial => rfl
      | candidate v =>
        have hne : v ≠ u := by intro h; apply hv; simp [h]
        simp [Ctx6.varVal, Ctx6.withParH, Ctx6.withPar, Ctx6.parOf, Par6.set, Par6.val, hne]

 theorem omitted_values_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X nm D H H') (e : Id × X.Ty) (he : e ∈ D)
    (v : X.Name) (hv : v ∈ (reqNames6 e.2).erase (.par nm)) : X.varVal H v = X.varVal H' v := by
  have hc := required_values_local_eq X nm D H H' h X.y₀ e he v (Finset.mem_of_mem_erase hv)
  simpa only [substituted_other_value X H nm X.y₀ v (Finset.mem_erase.mp hv).1,
    substituted_other_value X H' nm X.y₀ v (Finset.mem_erase.mp hv).1] using hc


 theorem label_law_values_eq (H H' : X.Hist) (S : Finset X.Name) (i : X.ι)
    (h : ∀ v ∈ S, X.varVal H v = X.varVal H' v) : X.labelLaw H S i = X.labelLaw H' S i := by
  have heq : X.reqNbhd H S = X.reqNbhd H' S := by
    ext y
    simp only [Ctx6.reqNbhd, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hy v hv
      rw [← h v hv]
      exact hy v hv
    · intro hy v hv
      rw [h v hv]
      exact hy v hv
  simp only [Ctx6.labelLaw, heq]

 theorem high_reference_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X (X.tgtName b) D H H') (e : Id × X.Ty) (he : e ∈ D) :
    X.highRef H b e.2 = X.highRef H' b e.2 := by
  have hl (i : X.ι) := label_law_values_eq X H H' ((reqNames6 e.2).erase (.par (X.tgtName b))) i
    (fun v hv => omitted_values_local_eq X (X.tgtName b) D H H' h e he v hv)
  unfold Ctx6.highRef Ctx6.tupleRef Ctx6.tupleLawOn
  congr 1
  funext i
  congr 1
  funext r
  exact hl i

 theorem high_likelihood_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X (X.tgtName b) D H H') (e : Id × X.Ty) (he : e ∈ D) (ξ : Fin N) (o : X.Tuple) :
    X.highLik H b ξ e.2 o = X.highLik H' b ξ e.2 o := by
  have ht := tag_post_local_eq X (X.tgtName b) D H H' h ξ e he
  have hr (i : X.ι) := label_law_values_eq X (X.withParH H (X.tgtName b) ξ)
    (X.withParH H' (X.tgtName b) ξ) (reqNames6 e.2) i
      (fun v hv => required_values_local_eq X (X.tgtName b) D H H' h ξ e he v hv)
  have hq (i : X.ι) := label_law_values_eq X H H' ((reqNames6 e.2).erase (.par (X.tgtName b))) i
    (fun v hv => omitted_values_local_eq X (X.tgtName b) D H H' h e he v hv)
  unfold Ctx6.highLik Ctx6.tupleRatio
  rw [ht, hr, hq]

 theorem high_weight_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X (X.tgtName b) D H H') (o : X.Data Id) (drop : Option (Id × X.Ty)) (ξ : Fin N) :
    X.highWeight H b D o drop ξ = X.highWeight H' b D o drop ξ := by
  have hp := prior_local_eq X (X.tgtName b) D H H' h
  have hg := propext (high_gate_local_iff X b D H H' h ξ)
  have hd := loc_density_local_eq X (X.tgtName b) D H H' h ξ
  unfold Ctx6.highWeight
  rw [hp, hg, hd]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  rw [high_likelihood_local_eq X b D H H' h e he ξ (o e)]

 theorem high_mass_local_eq {Id : Type} [Fintype Id] [DecidableEq Id]
    (b : X.State) (D : Finset (Id × X.Ty)) (H H' : X.Hist)
    (h : LocalAgree X (X.tgtName b) D H H') (o : X.Data Id) (drop : Option (Id × X.Ty))
    (hm : X.stMode b = .high) : X.s3Mass H b D o drop = X.s3Mass H' b D o drop := by
  unfold Ctx6.s3Mass
  apply Finset.sum_congr rfl
  intro ξ hξ
  simpa only [Ctx6.s3Weight, hm] using high_weight_local_eq X b D H H' h o drop ξ


end
end HypercubeRamsey.S06.Lane_sol_s06_g
