import HypercubeRamsey.S06.Steps_raw_sol_s06_g

namespace HypercubeRamsey.S06.Lane_sol_s06_g
open OAI.HypercubeRamsey Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 400000

variable {γ p₀ K : ℝ} {n N : ℕ} {E : Fin N → Fin N → Prop} {G : Colour} {M : TagMix N}
variable (X : Ctx6 γ p₀ K n N E G M)
variable {Id : Type} [Fintype Id] [DecidableEq Id]

abbrev LocalCandidates (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) :=
  {u : X.Bin // u ∈ X.locBins D nm} → Fin N
abbrev LocalTags (D : Finset (Id × X.Ty)) := {s : X.Key // s ∈ X.locKeys D} → X.ι
abbrev LocalHidden (D : Finset (Id × X.Ty)) := {ℓ : X.HKey // ℓ ∈ X.locHid D} → Fin N
abbrev LocalObs (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) :=
  LocalCandidates X nm D × LocalTags X D × LocalHidden X D

/-- Complete local observations with fixed exterior values. -/
def assembleLocal (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty))
    (l : LocalObs X nm D) : X.Hist :=
  ((v, Lane_sol_s06_steps1.fill (X.locBins D nm) l.1 (fun _ => X.y₀),
      Lane_sol_s06_steps1.fill (X.locKeys D) l.2.1 (fun _ => X.i₀)),
    Lane_sol_s06_steps1.fill (X.locHid D) l.2.2 (fun _ => X.y₀))

/-- Uniform law for an observed candidate or hidden scalar. -/
def labelReference : Law N := FinProb.uniform Finset.univ ⟨X.y₀, Finset.mem_univ _⟩

theorem labelReference_weight (y : Fin N) : (labelReference X).w y = (N : ℝ)⁻¹ := by
  simp [labelReference, FinProb.uniform]

/-- The product reference for the primitive local observations. -/
def localReference (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) : FinProb (LocalObs X nm D) :=
  (FinProb.pi fun _ : {u : X.Bin // u ∈ X.locBins D nm} => labelReference X).bind fun _ =>
    (FinProb.pi fun _ : {s : X.Key // s ∈ X.locKeys D} => tagLaw6 M).bind fun _ =>
      FinProb.pi fun _ : {ℓ : X.HKey // ℓ ∈ X.locHid D} => labelReference X

/-- The actual local kernels at a substituted named primary. -/
def localLaw (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N) :
    FinProb (LocalObs X nm D) :=
  let v' := match nm with | .initial => ξ | .candidate _ => v
  let base (A : LocalCandidates X nm D) (I : LocalTags X D) : X.Base :=
    (X.withParH (assembleLocal X v nm D (A, I, fun _ => X.y₀)) nm ξ).1
  (FinProb.pi fun _ : {u : X.Bin // u ∈ X.locBins D nm} => X.candLaw v').bind fun A =>
    (FinProb.pi fun s : {s : X.Key // s ∈ X.locKeys D} =>
      X.tagLawAt (X.parOf (base A (fun _ => X.i₀))) s.1).bind fun I =>
        FinProb.pi fun ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D} => X.hidPost (base A I) ℓ.1.1

theorem assemble_candidate (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty))
    (l : LocalObs X nm D) (u : X.Bin) (hu : u ∈ X.locBins D nm) :
    (assembleLocal X v nm D l).1.2.1 u = l.1 ⟨u, hu⟩ := by
  simp [assembleLocal, Lane_sol_s06_steps1.fill, hu]

theorem assemble_tag (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty))
    (l : LocalObs X nm D) (s : X.Key) (hs : s ∈ X.locKeys D) :
    (assembleLocal X v nm D l).1.2.2 s = l.2.1 ⟨s, hs⟩ := by
  simp [assembleLocal, Lane_sol_s06_steps1.fill, hs]

theorem assemble_hidden (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty))
    (l : LocalObs X nm D) (ℓ : X.HKey) (hℓ : ℓ ∈ X.locHid D) :
    (assembleLocal X v nm D l).2 ℓ = l.2.2 ⟨ℓ, hℓ⟩ := by
  simp [assembleLocal, Lane_sol_s06_steps1.fill, hℓ]

 theorem localReference_weight (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty))
    (l : LocalObs X nm D) :
    (localReference X nm D).w l =
      (∏ _u : {u : X.Bin // u ∈ X.locBins D nm}, (N : ℝ)⁻¹) *
      (∏ s : {s : X.Key // s ∈ X.locKeys D}, M.Λ (l.2.1 s)) *
      (∏ _ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D}, (N : ℝ)⁻¹) := by
  simp only [localReference, FinProb.bind, FinProb.pi, labelReference_weight, tagLaw6]
  ring

 theorem localLaw_weight (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (l : LocalObs X nm D) :
    (localLaw X v nm D ξ).w l =
      (∏ u : {u : X.Bin // u ∈ X.locBins D nm},
        (X.candLaw (X.withParH (assembleLocal X v nm D l) nm ξ).1.1).w (l.1 u)) *
      (∏ s : {s : X.Key // s ∈ X.locKeys D},
        (X.tagLawAt (X.parOf (X.withParH (assembleLocal X v nm D l) nm ξ).1) s.1).w (l.2.1 s)) *
      (∏ ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D},
        (X.hidPost (X.withParH (assembleLocal X v nm D l) nm ξ).1 ℓ.1.1).w (l.2.2 ℓ)) := by
  cases nm <;>
    simp only [localLaw, FinProb.bind, FinProb.pi, assembleLocal, Ctx6.withParH, Ctx6.withPar,
      Ctx6.parOf, Par6.set] <;> ring

 theorem prod_subtype {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I) (f : I → ℝ) :
    (∏ i : {i // i ∈ S}, f i.1) = ∏ i ∈ S, f i := by
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach S f

 theorem localDensity_weight (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (l : LocalObs X nm D) :
    X.locDensity (assembleLocal X v nm D l) nm D ξ =
      (∏ u : {u : X.Bin // u ∈ X.locBins D nm}, (N : ℝ) *
        (X.candLaw (X.withParH (assembleLocal X v nm D l) nm ξ).1.1).w (l.1 u)) *
      (∏ s : {s : X.Key // s ∈ X.locKeys D}, safeRatio6
        ((X.tagLawAt (X.parOf (X.withParH (assembleLocal X v nm D l) nm ξ).1) s.1).w (l.2.1 s))
        (M.Λ (l.2.1 s))) *
      (∏ ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D}, (N : ℝ) *
        (X.hidPost (X.withParH (assembleLocal X v nm D l) nm ξ).1 ℓ.1.1).w (l.2.2 ℓ)) := by
  have hc := prod_subtype (X.locBins D nm) (fun u => (N : ℝ) *
    (X.candLaw (X.withParH (assembleLocal X v nm D l) nm ξ).1.1).w ((assembleLocal X v nm D l).1.2.1 u))
  have ht := prod_subtype (X.locKeys D) (fun s => safeRatio6
    ((X.tagLawAt (X.parOf (X.withParH (assembleLocal X v nm D l) nm ξ).1) s).w ((assembleLocal X v nm D l).1.2.2 s))
    (M.Λ ((assembleLocal X v nm D l).1.2.2 s)))
  have hz := prod_subtype (X.locHid D) (fun ℓ => (N : ℝ) *
    (X.hidPost (X.withParH (assembleLocal X v nm D l) nm ξ).1 ℓ.1).w ((assembleLocal X v nm D l).2 ℓ))
  simp only [assemble_candidate X v nm D l _ (Subtype.property _)] at hc
  simp only [assemble_tag X v nm D l _ (Subtype.property _)] at ht
  simp only [assemble_hidden X v nm D l _ (Subtype.property _)] at hz
  dsimp only [Ctx6.withParH] at hc ht hz
  dsimp only [Ctx6.locDensity]
  rw [← hc, ← ht, ← hz]
  rfl


private theorem kernelRatio_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ safeRatio6 a b := by
  unfold safeRatio6
  split
  · exact le_rfl
  · exact div_nonneg ha hb

private theorem kernelRatio_weight_le {a b : ℝ} (ha : 0 ≤ a) : b * safeRatio6 a b ≤ a := by
  unfold safeRatio6
  by_cases hb : b = 0
  · simp [hb, ha]
  · simp [hb, mul_div_cancel₀]

 theorem primitive_density_le (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (l : LocalObs X nm D) :
    (localReference X nm D).w l * X.locDensity (assembleLocal X v nm D l) nm D ξ ≤
      (localLaw X v nm D ξ).w l := by
  let H := assembleLocal X v nm D l
  let B := (X.withParH H nm ξ).1
  let Aidx := {u : X.Bin // u ∈ X.locBins D nm}
  let Iidx := {s : X.Key // s ∈ X.locKeys D}
  let Zidx := {ℓ : X.HKey // ℓ ∈ X.locHid D}
  let a (u : Aidx) := (X.candLaw B.1).w (l.1 u)
  let i (s : Iidx) := (X.tagLawAt (X.parOf B) s.1).w (l.2.1 s)
  let z (ℓ : Zidx) := (X.hidPost B ℓ.1.1).w (l.2.2 ℓ)
  let r (s : Iidx) := safeRatio6 (i s) (M.Λ (l.2.1 s))
  have hn : (N : ℝ) ≠ 0 := by
    have hp : 0 < N := lt_of_le_of_lt (Nat.zero_le X.y₀.val) X.y₀.isLt
    exact ne_of_gt (by exact_mod_cast hp)
  have ha : (∏ _u : Aidx, (N : ℝ)⁻¹) * (∏ u : Aidx, (N : ℝ) * a u) = ∏ u : Aidx, a u := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro u hu
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hz : (∏ _ℓ : Zidx, (N : ℝ)⁻¹) * (∏ ℓ : Zidx, (N : ℝ) * z ℓ) = ∏ ℓ : Zidx, z ℓ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hi : (∏ s : Iidx, M.Λ (l.2.1 s)) * (∏ s : Iidx, r s) ≤ ∏ s : Iidx, i s := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀
      (fun s hs => mul_nonneg (M.Λ_nonneg _) (kernelRatio_nonneg ((X.tagLawAt _ s.1).nonneg _) (M.Λ_nonneg _)))
      (fun s hs => kernelRatio_weight_le ((X.tagLawAt _ s.1).nonneg _))
  have han : 0 ≤ ∏ u : Aidx, a u := Finset.prod_nonneg fun u hu => (X.candLaw B.1).nonneg _
  have hzn : 0 ≤ ∏ ℓ : Zidx, z ℓ := Finset.prod_nonneg fun ℓ hℓ => (X.hidPost B ℓ.1.1).nonneg _
  rw [localReference_weight, localDensity_weight, localLaw_weight]
  change ((∏ _u : Aidx, (N : ℝ)⁻¹) * (∏ s : Iidx, M.Λ (l.2.1 s)) * (∏ _ℓ : Zidx, (N : ℝ)⁻¹)) *
      ((∏ u : Aidx, (N : ℝ) * a u) * (∏ s : Iidx, r s) * (∏ ℓ : Zidx, (N : ℝ) * z ℓ)) ≤
    (∏ u : Aidx, a u) * (∏ s : Iidx, i s) * (∏ ℓ : Zidx, z ℓ)
  calc
    _ = ((∏ _u : Aidx, (N : ℝ)⁻¹) * (∏ u : Aidx, (N : ℝ) * a u)) *
        ((∏ s : Iidx, M.Λ (l.2.1 s)) * (∏ s : Iidx, r s)) *
        ((∏ _ℓ : Zidx, (N : ℝ)⁻¹) * (∏ ℓ : Zidx, (N : ℝ) * z ℓ)) := by ring
    _ ≤ _ := by rw [ha, hz]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi han) hzn

 theorem primitive_density_eq (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (l : LocalObs X nm D)
    (hΛ : ∀ s : {s : X.Key // s ∈ X.locKeys D}, M.Λ (l.2.1 s) ≠ 0) :
    (localReference X nm D).w l * X.locDensity (assembleLocal X v nm D l) nm D ξ =
      (localLaw X v nm D ξ).w l := by
  let H := assembleLocal X v nm D l
  let B := (X.withParH H nm ξ).1
  let Aidx := {u : X.Bin // u ∈ X.locBins D nm}
  let Iidx := {s : X.Key // s ∈ X.locKeys D}
  let Zidx := {ℓ : X.HKey // ℓ ∈ X.locHid D}
  let a (u : Aidx) := (X.candLaw B.1).w (l.1 u)
  let i (s : Iidx) := (X.tagLawAt (X.parOf B) s.1).w (l.2.1 s)
  let z (ℓ : Zidx) := (X.hidPost B ℓ.1.1).w (l.2.2 ℓ)
  let r (s : Iidx) := safeRatio6 (i s) (M.Λ (l.2.1 s))
  have hn : (N : ℝ) ≠ 0 := by
    have hp : 0 < N := lt_of_le_of_lt (Nat.zero_le X.y₀.val) X.y₀.isLt
    exact ne_of_gt (by exact_mod_cast hp)
  have ha : (∏ _u : Aidx, (N : ℝ)⁻¹) * (∏ u : Aidx, (N : ℝ) * a u) = ∏ u : Aidx, a u := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro u hu
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hz : (∏ _ℓ : Zidx, (N : ℝ)⁻¹) * (∏ ℓ : Zidx, (N : ℝ) * z ℓ) = ∏ ℓ : Zidx, z ℓ := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hi : (∏ s : Iidx, M.Λ (l.2.1 s)) * (∏ s : Iidx, r s) = ∏ s : Iidx, i s := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro s hs
    dsimp [r]
    simp only [safeRatio6, if_neg (hΛ s)]
    field_simp [hΛ s]
  rw [localReference_weight, localDensity_weight, localLaw_weight]
  change ((∏ _u : Aidx, (N : ℝ)⁻¹) * (∏ s : Iidx, M.Λ (l.2.1 s)) * (∏ _ℓ : Zidx, (N : ℝ)⁻¹)) *
      ((∏ u : Aidx, (N : ℝ) * a u) * (∏ s : Iidx, r s) * (∏ ℓ : Zidx, (N : ℝ) * z ℓ)) =
    (∏ u : Aidx, a u) * (∏ s : Iidx, i s) * (∏ ℓ : Zidx, z ℓ)
  calc
    _ = ((∏ _u : Aidx, (N : ℝ)⁻¹) * (∏ u : Aidx, (N : ℝ) * a u)) *
        ((∏ s : Iidx, M.Λ (l.2.1 s)) * (∏ s : Iidx, r s)) *
        ((∏ _ℓ : Zidx, (N : ℝ)⁻¹) * (∏ ℓ : Zidx, (N : ℝ) * z ℓ)) := by ring
    _ = _ := by rw [ha, hz, hi]



 theorem localLaw_positive_factors (v : Fin N) (nm : ParentName6 X.Bin) (D : Finset (Id × X.Ty)) (ξ : Fin N)
    (l : LocalObs X nm D) (hp : 0 < (localLaw X v nm D ξ).w l) :
    (∀ u : {u : X.Bin // u ∈ X.locBins D nm},
      0 < (X.candLaw (X.withParH (assembleLocal X v nm D l) nm ξ).1.1).w (l.1 u)) ∧
    (∀ s : {s : X.Key // s ∈ X.locKeys D},
      0 < (X.tagLawAt (X.parOf (X.withParH (assembleLocal X v nm D l) nm ξ).1) s.1).w (l.2.1 s)) ∧
    (∀ ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D},
      0 < (X.hidPost (X.withParH (assembleLocal X v nm D l) nm ξ).1 ℓ.1.1).w (l.2.2 ℓ)) := by
  let B := (X.withParH (assembleLocal X v nm D l) nm ξ).1
  let a : ℝ := ∏ u : {u : X.Bin // u ∈ X.locBins D nm}, (X.candLaw B.1).w (l.1 u)
  let i : ℝ := ∏ s : {s : X.Key // s ∈ X.locKeys D}, (X.tagLawAt (X.parOf B) s.1).w (l.2.1 s)
  let z : ℝ := ∏ ℓ : {ℓ : X.HKey // ℓ ∈ X.locHid D}, (X.hidPost B ℓ.1.1).w (l.2.2 ℓ)
  have ha : 0 ≤ a := Finset.prod_nonneg fun u hu => (X.candLaw B.1).nonneg _
  have hi : 0 ≤ i := Finset.prod_nonneg fun s hs => (X.tagLawAt _ s.1).nonneg _
  have hz : 0 ≤ z := Finset.prod_nonneg fun ℓ hℓ => (X.hidPost B ℓ.1.1).nonneg _
  have hprod : 0 < a * i * z := by simpa only [localLaw_weight] using hp
  have hai : 0 < a * i := (mul_pos_iff.mp hprod).elim (fun h => h.1)
    (fun h => False.elim (not_lt_of_ge (mul_nonneg ha hi) h.1))
  have haz : 0 < a := (mul_pos_iff.mp hai).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge ha h.1))
  have hiz : 0 < i := (mul_pos_iff.mp hai).elim (fun h => h.2) (fun h => False.elim (not_lt_of_ge hi h.2))
  have hzz : 0 < z := (mul_pos_iff.mp hprod).elim (fun h => h.2)
    (fun h => False.elim (not_lt_of_ge hz h.2))
  exact ⟨Lane_q_s06_steps1.prod_pos_each6 _ (fun u => (X.candLaw B.1).nonneg _) haz,
    Lane_q_s06_steps1.prod_pos_each6 _ (fun s => (X.tagLawAt _ s.1).nonneg _) hiz,
    Lane_q_s06_steps1.prod_pos_each6 _ (fun ℓ => (X.hidPost B ℓ.1.1).nonneg _) hzz⟩


end
end HypercubeRamsey.S06.Lane_sol_s06_g
